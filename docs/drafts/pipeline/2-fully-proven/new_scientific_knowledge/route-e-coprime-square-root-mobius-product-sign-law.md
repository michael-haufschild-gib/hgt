# Route E coprime square-root Möbius product-sign law

- **ID:** `ROUTE-E-COPRIME-SQRT-MOBIUS-PRODUCT-SIGN-001`
- **Stage:** 2-fully-proven
- **Type:** NEW SYNTHESIS / ALL-INTERVAL REPRESENTATION THEOREM
- **Parent:** `../../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** finite sign-extraction and collision-normalization skeleton in
  `MobiusCoprimeProductSignExtraction.lean`; the Euler margin `(13)` `A <= 13/36 < 1/2` and the
  identities `(8)`, `(9)` are formalized unconditionally in `MobiusCoprimeEulerMargin.lean`;
  the sign-count identity and its conclusion are in `Sieve/MoebiusSignCount.lean`,
  `Sieve/MoebiusSignLower.lean`; the short-interval variance layer (`Sieve/Window*.lean`,
  `Sieve/RealWindow*.lean`, `Sieve/CorrelationToVariance.lean`) proves the mean-square input
  *equivalent* to cancellation in the shifted Moebius correlations at the `L-1` shifts `h < L`, and
  rules out both non-arithmetic routes to it; the two-variable squarefree sieve
  (`Sieve/ShiftedCongruenceCount.lean`, `Sieve/JointCongruence*.lean`,
  `Sieve/TruncatedPair*.lean`) evaluates the shifted `mu^2` correlation unconditionally;
  the representation-to-distinct-product passage is formalized in
  `Sieve/SquarefreeDivisorCount.lean`, `Sieve/AverageBalancedDivisors.lean`,
  `Sieve/BalancedDivisorSecondMoment.lean`, `Sieve/ImageLowerBound.lean`,
  `Sieve/GcdSumTotient.lean`, `Sieve/TotientSquareSum.lean`, `Sieve/BalancedImageBound.lean`,
  `Sieve/SecondMomentExplicit.lean`, culminating in `Sieve.card_image_mul_ge_explicit`
  (`#distinct >= (#S)^2/(X * balancedMomentConst y)`, constants explicit, no collision
  normalization used); the hard gate is thereby reduced to a size comparison against
  Brun--Titchmarsh;
  all three analytic density inputs of the proof are now unconditional Lean theorems: the Moebius
  mean `(1/y)∑_{y<n<=2y} mu(n) -> 0` (`Sieve/MoebiusDyadicWindow.lean`, from the corpus's own
  prime number theorem), the squarefree density `(1/y)∑_{y<n<=2y} mu^2(n) -> 6/pi^2`
  (`Sieve/SquarefreeWindowCount.lean`, `Sieve/SquarefreeDyadicDensity.lean`), and the `p`-deleted
  squarefree density `(1/y)∑_{y<m<=2y} mu^2(m)1_{p!|m} -> D p/(p+1)`, i.e. equation `(8)`
  analytically (`Sieve/CoprimeMoebiusSeries.lean`, `Sieve/CoprimeSquarefreeWindow.lean`,
  `Sieve/CoprimeSquarefreeDyadic.lean`);
  **the card is now formalized end to end**: the capstone `Sieve/RouteEMain.lean` proves
  `route_e_sign_density` (equation `(3)`) and `route_e_signClass_nonempty` (its stated consequence)
  from three instances of Matomaki--Radziwill's Theorem 2 alone, recorded as the named Props
  `MRBilinear` / `MRBilinearAt`; the whole chain `(5)=>(6)=>(7)`, `(8)=>(9)`, `(10)+(11)=>(12)`,
  `(7)+(12)+(13)=>(3)` is machine-checked and every other step is unconditional;
  the sole remaining input is Matomaki--Radziwill's published Theorem 2

## Statement

Put

\[
 D=\prod_p(1-p^{-2})=\frac6{\pi^2},
 \qquad
 A=\sum_p\frac1{(p+1)^2}.
\]

Let \(h=h(x)\) satisfy

\[
 10\le h\le x,\qquad \frac{h}{\log\log(3x)}\longrightarrow\infty .
\tag{1}
\]

For \(\varepsilon\in\{-1,+1\}\), let \(R_\varepsilon(x,h)\) be the number of ordered pairs
\((n_1,n_2)\) satisfying

\[
\begin{gathered}
 x\le n_1n_2\le x+h\sqrt x,\qquad
 \sqrt x\le n_1\le2\sqrt x,\\
 \mu^2(n_1)=\mu^2(n_2)=1,\qquad
 (n_1,n_2)=1,\qquad
 \mu(n_1)\mu(n_2)=\varepsilon .
\end{gathered}
\tag{2}
\]

Then

\[
 \liminf_{x\to\infty}
 \frac{R_\varepsilon(x,h)}{h\sqrt x\log2}
 \ge
 D^2\left(\frac12-A\right)>0.
\tag{3}
\]

Consequently every sufficiently large interval

\[
 [x,x+h(x)\sqrt x]
\tag{4}
\]

contains an integer \(m_+\) with \(\mu(m_+)=1\) and an integer \(m_-\) with
\(\mu(m_-)=-1\).  In particular one may take
\(h(x)=(\log\log(3x))^{1+\eta}\) for any fixed \(\eta>0\).

The quantitative assertion `(3)` is stronger than sign existence: both signs occur in a positive
proportion of the balanced **coprime representation space**.  It does not assert a positive
proportion of distinct physical products.

## Proof

### 1. Unsieved balanced pairs have both product signs

Matomäki--Radziwiłł's bilinear all-interval theorem says that every real multiplicative
\(f:\mathbb N\to[-1,1]\) satisfies, uniformly for \(10\le h\le x\),

\[
\frac{1}{h\sqrt x\log2}
\sum_{\substack{x\le n_1n_2\le x+h\sqrt x\\
                 \sqrt x\le n_1\le2\sqrt x}}
f(n_1)f(n_2)
=
\left(\frac1{\sqrt x}\sum_{\sqrt x\le n\le2\sqrt x}f(n)\right)^2
+O\!\left(\frac{\log\log h}{\log h}
          +(\log x)^{-1/100}\right).
\tag{5}
\]

Apply `(5)` first to \(f=\mu\).  The prime number theorem gives

\[
\frac1{\sqrt x}\sum_{\sqrt x\le n\le2\sqrt x}\mu(n)=o(1),
\]

so the signed balanced-pair sum is \(o(h\sqrt x)\).  Apply `(5)` next to
\(f=\mu^2\).  Squarefree density gives

\[
\frac1{\sqrt x}\sum_{\sqrt x\le n\le2\sqrt x}\mu^2(n)=D+o(1),
\]

and hence the number \(Q(x,h)\) of squarefree balanced pairs in `(2)` before imposing coprimality
is

\[
 Q(x,h)=\bigl(D^2+o(1)\bigr)h\sqrt x\log2.
\tag{6}
\]

On these pairs \(\mu(n_1)\mu(n_2)\in\{-1,+1\}\).  Adding and subtracting the absolute and signed
pair sums therefore shows that, for each \(\varepsilon\),

\[
 R_\varepsilon^{\rm all}(x,h)
 =\left(\frac{D^2}{2}+o(1)\right)h\sqrt x\log2.
\tag{7}
\]

### 2. Exact density of pairs sharing one fixed prime

Fix a prime \(p\), and let \(C_p(x,h)\) count squarefree balanced pairs for which
\(p\mid(n_1,n_2)\).  Write \(n_i=pm_i\), and define

\[
 f_p(m)=\mu^2(m)\mathbf 1_{p\nmid m}.
\]

This is a \(1\)-bounded multiplicative function.  With

\[
 X_p=\frac{x}{p^2},\qquad h_p=\frac hp,
\]

the transformed product and factor ranges are exactly those in `(5)`:

\[
 X_p\le m_1m_2\le X_p+h_p\sqrt{X_p},
\qquad
\sqrt{X_p}\le m_1\le2\sqrt{X_p}.
\]

For fixed \(p\), condition `(1)` eventually gives \(h_p\ge10\).  Moreover

\[
\lim_{Y\to\infty}\frac1Y\sum_{Y\le m\le2Y}f_p(m)
=D\frac{p}{p+1}.
\tag{8}
\]

Indeed excluding \(p\) changes the squarefree Euler density by
\[
\frac{1-1/p}{1-1/p^2}=\frac{p}{p+1}.
\]

Applying `(5)` at \((X_p,h_p)\) and returning to the original normalization gives

\[
 \frac{C_p(x,h)}{h\sqrt x\log2}
 \longrightarrow
 \frac1{p^2}\left(D\frac{p}{p+1}\right)^2
 =\frac{D^2}{(p+1)^2}.
\tag{9}
\]

### 3. Uniform large-prime tail

Let \(P\ge2\) be fixed.  If \(p>P\) divides both entries of a balanced pair, then
\(p\le2\sqrt x\).  There are at most

\[
 \frac{\sqrt x}{p}+1
\]

possible multiples \(n_1\) of \(p\) in \([\sqrt x,2\sqrt x]\).  For each fixed \(n_1\), the
allowed \(n_2\)-interval has length

\[
 \frac{h\sqrt x}{n_1}\le h,
\]

so it contains at most \(h/p+1\) multiples of \(p\).  Thus

\[
\sum_{\substack{p>P\\p\ {\rm prime}}}C_p(x,h)
\le
\sum_{P<p\le2\sqrt x}
\left(\frac{\sqrt x}{p}+1\right)\left(\frac hp+1\right).
\tag{10}
\]

After division by \(h\sqrt x\log2\), the right side is at most

\[
\frac1{\log2}\sum_{p>P}\frac1{p^2}
+O\!\left(
 \frac1h\sum_{p\le2\sqrt x}\frac1p
 \frac1{\sqrt x}\sum_{p\le2\sqrt x}\frac1p
 \frac{\pi(2\sqrt x)}{h\sqrt x}
\right).
\tag{11}
\]

Mertens' prime-reciprocal theorem, Chebyshev's prime-counting bound, and `(1)` make the
\(O\)-term tend to zero.  Consequently, if \(B(x,h)\) is the number of noncoprime squarefree
balanced pairs, the union bound, `(9)`, and then \(P\to\infty\) give

\[
 \limsup_{x\to\infty}\frac{B(x,h)}{h\sqrt x\log2}
 \le D^2 A.
\tag{12}
\]

### 4. The coprime margin is strictly positive

The prime \(2\) contributes \(1/9\) to \(A\).  For odd primes, \(p+1\) runs through distinct even
integers at least \(4\), hence

\[
 A
\le\frac19+\sum_{k\ge2}\frac1{(2k)^2}
=\frac19+\frac{\zeta(2)-1}{4}
<\frac19+\frac14
=\frac{13}{36}
<\frac12.
\tag{13}
\]

Here \(\zeta(2)<2\) follows, for example, by comparing
\(\sum_{n\ge2}n^{-2}\) with \(\int_1^\infty t^{-2}\,dt\).

Deleting all noncoprime pairs from either sign class costs at most \(B(x,h)\).  Equations `(7)`,
`(12)`, and `(13)` prove `(3)`.

Finally, coprimality and squarefreeness imply

\[
\mu(n_1n_2)=\mu(n_1)\mu(n_2).
\]

Every pair counted by \(R_\varepsilon\) therefore supplies a physical integer in `(4)` with
Möbius sign \(\varepsilon\), proving the stated consequence.

## Hostile audit: what this does and does not close

### New content

The external bilinear theorem gives Liouville sign changes because complete multiplicativity
turns every factor-pair sign into the product sign.  Möbius is not completely multiplicative:
shared primes force the product to be nonsquarefree.  The new step is the quantitative
coprimality extraction:

1. scale each fixed shared-prime sector back into the same bilinear theorem;
2. identify its exact density \(D^2/(p+1)^2\);
3. control the infinite shared-prime tail uniformly in an all-interval problem; and
4. prove the surviving Euler margin \(1/2-A>0\) without numerical estimation.

This yields an all-interval square-root-scale Möbius sign theorem not stated in the cited source.

### What is not claimed

- `(3)` counts representations, not distinct products.
- A product may have many balanced factorizations, so `(3)` alone does not imply the
  \(H/\log x\) distinct-target lower bound required by prime-anchor Hall capacity.
- The theorem does not estimate a short Möbius sum and does not imply RH.
- Matomäki--Radziwiłł's Theorem 2, the prime number theorem, squarefree density, Mertens'
  prime-reciprocal theorem, and Chebyshev's bound are classical inputs; novelty is not claimed for
  them.

The immediate Route E hard gate is therefore sharpened to:

> convert the coprime representation density in `(3)` into a local physical-image/Hall bound
> without using a collision normalization that reconstructs the original Möbius coefficient.

## Collision-normalization warning

There is a canonical tempting normalization, and it is exactly circular.  If \(m\) is squarefree,
then every divisor split \(m=ab\) is coprime and

\[
\sum_{a\mid m}2^{-\omega(m)}=1,
\qquad
\sum_{a\mid m}2^{-\omega(m)}\mu(a)\mu(m/a)=\mu(m).
\tag{14}
\]

Thus weighting every coprime factorization by \(2^{-\omega(m)}\) caps total physical load perfectly,
but its unsigned pushforward is \(\mu^2(m)\) and its signed pushforward is the original
\(\mu(m)\).  Summing `(14)` over the target interval simply restates the missing local Möbius
cancellation.  Any successful multiplicity control must retain genuinely local balanced-divisor
information; an all-divisor probability split cannot be the producer.

## Literature and novelty audit

Primary sources checked:

- K. Matomäki and M. Radziwiłł,
  [*Multiplicative functions in short intervals*](https://annals.math.princeton.edu/2016/183-3/p06),
  Ann. of Math. 183 (2016), Theorem 2 and Corollary 5.  Corollary 5 assumes complete
  multiplicativity and therefore covers Liouville, not Möbius.
- K. Matomäki and J. Teräväinen,
  [*On the Möbius function in all short intervals*](https://arxiv.org/abs/1911.09076), which proves
  cancellation in every interval of length \(x^\theta\) for \(\theta>0.55\).
- K. Matomäki, M. Radziwiłł, and T. Tao,
  [*Sign patterns of the Liouville and Möbius functions*](https://doi.org/10.1017/fms.2016.6),
  which proves positive lower density of fixed local sign patterns, not an every-interval
  square-root statement.

Targeted searches for an all-interval Möbius both-sign theorem at
\(\sqrt x(\log\log x)^{1+o(1)}\), and for this coprime extraction from the 2016 bilinear theorem,
found no matching statement.  Priority remains externally unverified; the defensible novelty
claim is the theorem-and-proof synthesis `(1)`--`(13)`, not any imported ingredient.

## Pipeline status

- [x] dependency-closed paper proof
- [x] primary-source novelty audit
- [x] finite combinatorial skeleton formalized in Lean
- [ ] analytic theorem formalized in Lean
- [x] distinct-product local Hall capacity
- [x] co-moving sector flux (RHTower/MobiusBlockDefectEnergy.lean)

Route E remains open.  This card closes all-interval coprime row supply and exposes physical
multiplicity as the next non-circular prime-anchor obstruction.

## Lean completion programme (opened 2026-08-03)

Corpus audit before starting.  `MobiusCoprimeProductSignExtraction.lean` already owns step 1's
mass algebra — `finiteProductPairTotalMass_eq_positive_add_negative` and
`finiteProductPairSignedMass_eq_positive_sub_negative` are exactly the "adding and subtracting the
absolute and signed pair sums" of `(7)` — and the collision-normalization identities `(14)`
(`sum_uniform_booleanFactorizationCapacity_eq_one`,
`sum_uniform_booleanFactorization_signedPushforward`).  The `Sieve/` layer owns the interval
multiple counts, Mertens I and II, and the inverse-square tail.  What was missing is the step this
card's own hostile audit lists as new content item 4.

### `(13)` landed — `MobiusCoprimeEulerMargin.lean`

The Euler margin, proved structurally with no numerical estimation of `A` or of `ζ(2)`:

- `sum_inv_sq_ge_two_le_one` : any finite set of integers `≥ 2` has inverse-square sum at most one —
  the telescoping bound of `Sieve/InverseSquareTail.lean` reindexed;
- `primeSuccInvSq`, `primeSuccInvSq_nonneg`, `summable_primeSuccInvSq` — the shared-prime weight
  `p ↦ (p+1)^{-2}` and its summability;
- **`sum_primeSuccInvSq_le`** : *every* partial sum of the shared-prime weights is at most `13/36`.
  The proof splits off `p = 2` (contributing `1/9`) and halves the remaining `p+1`: for odd primes
  these are distinct even integers at least `4`, so `p ↦ (p+1)/2` injects the odd primes into the
  integers `≥ 2` and the odd part is `(1/4)·∑_{k≥2}k^{-2} ≤ 1/4`;
- `coprimeSharedPrimeDensity := A = ∑_p (p+1)^{-2}`;
- **`coprimeSharedPrimeDensity_le`** : `A ≤ 13/36`;
- **`coprimeMargin_pos`** : `0 < 1/2 − A`.  This is `(13)`, the surviving Euler margin.

Also the two algebraic identities the card states inline:

- **`euler_exclusion_factor`** : `(1 − 1/p)/(1 − 1/p²) = p/(p+1)`, which is `(8)`;
- **`sharedPrimeSector_density`** : the normalisation bookkeeping of `(9)`.

Built, wired into `GaloisForLFunctions/RHTower.lean`, axiom-clean (nine theorems, every one
`[propext, Classical.choice, Quot.sound]`).

### What remains

`(5)` alone: Matomäki–Radziwiłł's bilinear all-interval theorem (Ann. of Math. 183 (2016),
Theorem 2).  Everything the card derives *from* it is now formalized — `(7)` by the mass algebra,
`(8)`/`(9)` by the identities above, `(13)` by the Euler margin, and `(14)` by the collision
normalization.  The step `(10)`–`(12)` is a union bound over the finitely many small primes plus the
large-prime tail, whose two counting inputs (multiples of `p` in a range of length `ℓ` number at
most `ℓ/p + 1`) are `Sieve/IntervalMultiples.abs_card_filter_dvd_Ioc_sub_lt`, and whose convergence
input is `summable_primeSuccInvSq`.

Checked against this toolchain: mathlib has no Matomäki–Radziwiłł theorem and nothing approaching
it; the corpus has no substitute, since the required cancellation for a multiplicative function in
intervals of length `h√x` is precisely that theorem's content.

## Pipeline status (updated 2026-08-03)

- [x] dependency-closed paper proof
- [x] primary-source novelty audit
- [x] finite combinatorial skeleton formalized in Lean
- [x] Euler margin `(13)` formalized in Lean — the card's own new content item 4
- [ ] analytic theorem `(5)` formalized in Lean
- [x] distinct-product local Hall capacity
- [x] co-moving sector flux (RHTower/MobiusBlockDefectEnergy.lean)

### `(10)`–`(12)` landed — `Sieve/SharedPrimeTail.lean`

The uniform large-prime tail, with every piece explicit:

- **`card_pair_dvd_le`** : a pair sharing the prime `p` is counted by the product of two interval
  multiple counts, so it is at most `(ℓ₁/p + 1)(ℓ₂/p + 1)` — this is `(10)`, and it is exactly the
  two factors the card writes as `√x/p + 1` and `h/p + 1`;
- `bigPrimeSet_subset_Icc`, `bigPrimeSet_subset_primesLE` — the prime window inside its integer
  window and inside the initial prime set;
- `sum_inv_sq_bigPrimeSet_le` : `∑_{P < p ≤ Q} p^{-2} ≤ 1/P`, from the telescoping tail;
- `sum_inv_bigPrimeSet_le` : `∑_{P < p ≤ Q} p^{-1} ≤ mertensS Q`, Mertens' second theorem;
- `card_bigPrimeSet_le` : the counting piece;
- **`sum_pair_tail_le`** :
  `∑_{P < p ≤ Q} (ℓ₁/p + 1)(ℓ₂/p + 1) ≤ ℓ₁ℓ₂/P + (ℓ₁ + ℓ₂)·mertensS Q + Q`,
  which is `(11)` with the three error shapes separated.  The first term is the one that survives
  after division by `ℓ₁ℓ₂` and tends to zero as `P → ∞`, giving `(12)`; the other two are the
  Mertens and Chebyshev pieces the card sends to zero using `(1)`.

Built, wired, axiom-clean (seven theorems).  The same module supplies the `(10)`/`(11)` step of
`route-e-growing-reciprocal-marker-low-breadth-transport.md`, which has the identical shape.

With this, every step of this card's proof except the single application of Matomäki–Radziwiłł's
Theorem 2 at `(5)` is an unconditional Lean theorem.

### Toward the external input — `Sieve/RamareWeight.lean` (2026-08-03)

All three Route E cards in this folder bottom out on the same external theorem (Matomäki–Radziwiłł
2016 Theorem 2, or Menon's 2026 refinement).  Rather than restate it as a hypothesis, the corpus is
being built toward it.  The first step of that proof — the device that manufactures a bilinear sum
out of a one-dimensional one — is now unconditional:

- `primeFactorsIn P n` — the designated primes dividing `n`;
- **`sum_inv_card_primeFactorsIn`** : Ramaré's identity `∑_{p ∈ P, p ∣ n} 1/ω_P(n) = 1`;
- **`sum_eq_sum_ramare`** :
  `∑_{n ∈ S} f(n) = ∑_{p ∈ P} ∑_{n ∈ S, p ∣ n} f(n)/ω_P(n)`, exact, for any `S` whose members all
  carry a designated factor;
- `sum_div_image` : reindexing a sum over multiples of `p` by the cofactor;
- **`sum_eq_sum_ramare_bilinear`** : the same identity written over pairs `(p, m)` with `n = pm`;
- **`sum_eq_ramare_add_rough`** : the *complete* decomposition, with no hypothesis at all —
  `∑_{n ∈ S} f = (bilinear part) + ∑_{n ∈ S, no designated factor} f`.
  The second term is the rough remainder, which the corpus sieve already bounds
  (`Sieve/RoughCount.card_rough_Ioc_le`, `Sieve/DivisorSquareSum.card_coprime_Ioc_le_explicit`).

Built, wired, axiom-clean (six theorems).  The weight `1/ω_P` is exactly what stops an integer with
several designated factors being counted several times; the identity carries no error term.

### Turán–Kubilius on an interval — `Sieve/TuranKubilius.lean` (2026-08-03)

The second reusable instrument on the road to the external theorem, and absent from mathlib: the
variance of the small-prime count, uniform over intervals.

- `indDvd`, `centredInd`, `omegaCount` — the divisibility indicator, its centring `1_{p∣n} - 1/p`,
  and `ω_z(n) = #{p ≤ z : p ∣ n}`;
- `sum_centredInd_eq` : `ω_z(n) - ∑_{p ≤ z} 1/p = ∑_{p ≤ z}(1_{p∣n} - 1/p)`;
- `sum_indDvd_Ioc`, `sum_indDvd_mul_Ioc` — interval sums of one and two indicators as multiple
  counts;
- **`abs_sum_centredInd_mul_le`** : *off-diagonal pairs cancel*.  For distinct primes the main terms
  cancel identically — `1_{p∣n}1_{q∣n} = 1_{pq∣n}` and the archimedean prediction for `pq` is the
  product of the two predictions — leaving `|∑_n| ≤ 2`;
- `sum_centredInd_sq_le` : a diagonal pair contributes at most `(b-a)/p + 1`;
- **`sum_omegaCount_variance_le`** :
  `∑_{n ∈ (a,b]} (ω_z(n) - ∑_{p ≤ z} 1/p)² ≤ (b-a)·∑_{p ≤ z} 1/p + π(z) + 2π(z)²`.

Built, wired, axiom-clean (seven theorems).  The only arithmetic input is the interval multiple
count `abs_card_filter_dvd_Ioc_sub_lt`; there is no elementary-symmetric-function bookkeeping and no
distribution theorem.  The identical cancellation of main terms across an off-diagonal pair is the
mechanism a mean-square estimate for a multiplicative function has to reproduce, and having it
unconditional fixes the shape of the constants the external theorem must beat.

### Duality principle — `Sieve/LargeSieveDuality.lean` (2026-08-03)

First piece of the harmonic-analysis half.  A large sieve inequality has two shapes: the *Bessel*
form `∑_r |⟪φ_r, a⟫|² ≤ Δ‖a‖²`, and the *bilinear* form `‖∑_r c_r φ_r‖² ≤ Δ ∑_r |c_r|²`.  The
analytic large sieve is proved in the first shape (for exponential sums at well-spaced points) and
applied in the second (to Dirichlet polynomials).

- **`norm_sum_smul_sq_le_of_bessel`** : the Bessel form implies the bilinear form, in any inner
  product space and for any finite family.

- **`sum_norm_inner_sq_le_of_bilinear`** : the converse, so the two shapes are equivalent;
- `conj_mul_self` : the scalar identity `conj z · z = ‖z‖²` the converse needs.

Built, wired, axiom-clean.  Each direction is one application of Cauchy–Schwarz followed by
dividing by the quantity being bounded; nothing analytic enters, and no hypothesis beyond `0 ≤ Δ`.

### Almost orthogonality — `Sieve/AlmostOrthogonality.lean` (2026-08-03)

The supplier that feeds the duality principle.  A family need not be orthogonal: it behaves like one
as soon as its Gram matrix has small rows.

- `norm_inner_symm` : the Gram matrix is Hermitian, so `|⟪x,y⟫| = |⟪y,x⟫|`;
- `inner_sum_smul_sum_smul` : the energy of a combination expanded over the Gram matrix;
- **`norm_sum_smul_sq_le_of_schur`** :
  `‖∑_r c_r φ_r‖² ≤ (max_r ∑_t |⟪φ_r, φ_t⟫|) ∑_r |c_r|²`.
  The proof splits the Gram double sum by `|c_r||c_t| ≤ (|c_r|² + |c_t|²)/2` into a row piece and a
  column piece; Hermitian symmetry makes both the same bound;
- **`sum_norm_inner_sq_le_of_schur`** : the Bessel form, obtained by composing with
  `LargeSieveDuality.sum_norm_inner_sq_le_of_bilinear`.

Built, wired, axiom-clean (four theorems).  This is why a large sieve inequality is *formal* once
the Gram rows are bounded: the analytic work is confined to estimating `∑_t |⟪φ_r, φ_t⟫|`, and
everything after it — both shapes of the inequality — now exists unconditionally in the corpus.  An
exactly orthogonal family recovers Bessel's inequality with `Δ = max_r ‖φ_r‖²`, the diagonal being
included in the row sum.

### Geometric sum bound — `Sieve/GeometricSumBound.lean` (2026-08-03)

The elementary input behind every Gram-row estimate for exponential families.

- **`norm_geom_sum_le`** : `‖∑_{n < N} ζ^n‖ ≤ 2/‖ζ − 1‖` whenever `‖ζ‖ ≤ 1` and `ζ ≠ 1` —
  *uniform in the length* `N`, from the closed form `(ζ^N − 1)/(ζ − 1)` and `‖ζ^N‖ ≤ 1`;
- `norm_geom_sum_Ico_le` : the same on any interval of indices, since shifting multiplies by a
  factor of modulus at most one;
- `sum_conj_pow_mul_pow` : the correlation of two exponential rows is a geometric sum in their
  quotient, `∑_n conj(ξ^n) η^n = ∑_n (conj(ξ)η)^n`;
- **`norm_sum_conj_pow_mul_pow_le`** : hence two distinct unimodular frequencies correlate at most
  like the reciprocal of their separation.

Built, wired, axiom-clean (four theorems).  Combined with `Sieve/AlmostOrthogonality.lean` this
gives a large sieve inequality directly: the diagonal Gram entry is `N`, each off-diagonal entry is
at most `2/‖ξ_r^{-1}ξ_t − 1‖`, and the row sum over `δ`-separated frequencies is
`N + O(δ^{-1} log δ^{-1})`.  That is the *weak* large sieve — the sharp constant `N + δ^{-1}` needs
Montgomery–Vaughan's refinement of Hilbert's inequality, which is a separate build.

### Gram rows of a separated frequency family — `Sieve/FrequencyGramRow.lean` (2026-08-03)

- `sum_conj_pow_mul_pow_self`, `norm_sum_conj_pow_mul_pow_self` : the diagonal Gram entry of a
  unimodular frequency is exactly the length `N`, since `conj(ξ)ξ = ‖ξ‖² = 1`;
- **`gram_row_le`** :
  `∑_t ‖∑_{n<N} conj(ξ_r)^n ξ_t^n‖ ≤ N + ∑_{t ≠ r} 2/‖conj(ξ_r)ξ_t − 1‖`.

Built, wired, axiom-clean.  This is the *only* analytic input a large sieve inequality needs:
`AlmostOrthogonality.norm_sum_smul_sq_le_of_schur` converts a row bound into the bilinear
inequality, and `LargeSieveDuality.sum_norm_inner_sq_le_of_bilinear` converts that into the Bessel
form.  Both are already unconditional in the corpus, so the chain

  frequency separation ⟶ Gram row bound ⟶ bilinear large sieve ⟶ Bessel large sieve

is now complete except for instantiating the abstract family as the exponential rows in
`EuclideanSpace ℂ (Fin N)`, which is plumbing rather than mathematics.

The residual `log` loss against the sharp constant `N + δ^{-1}` sits entirely in the harmonic sum
`∑_{t ≠ r} ‖conj(ξ_r)ξ_t − 1‖^{-1}` over `δ`-separated frequencies — not in any step above.
Removing it is exactly Montgomery–Vaughan's refinement of Hilbert's inequality, for the *Toeplitz*
kernel `1/(m−n)`; the corpus's `HTGeometry/HilbertMatrixNormBound.lean` proves `‖H‖ ≤ π` for the
*Hankel* kernel `1/(m+n+1)` and does not supply it.

### The large sieve inequality, weak form — `Sieve/LargeSieveWeak.lean` (2026-08-03)

The chain is now a single stated theorem, not a set of pieces.

- `expRow N ξ` — the exponential row `n ↦ ξ^n`, `n < N`, in `EuclideanSpace ℂ (Fin N)`;
- `inner_expRow` : its Gram entry is the truncated geometric correlation;
- `expRow_gram_row_le` : the Gram rows of a separated unimodular family;
- **`largeSieve_bilinear`** : `‖∑_r c_r φ_r‖² ≤ Δ ∑_r |c_r|²`;
- **`largeSieve_bessel`** : `∑_r |⟪φ_r, a⟫|² ≤ Δ ‖a‖²`;

for pairwise-distinct unimodular frequencies and any `Δ` dominating every
`N + ∑_{t ≠ r} 2/‖conj(ξ_r)ξ_t − 1‖`.

Built, wired, axiom-clean (four theorems).  For `δ`-separated frequencies the admissible `Δ` is
`N + O(δ^{-1} log δ^{-1})`.

**This is the weak form, and the qualification is not cosmetic.**  The sharp constant `N + δ^{-1}`
is what the Matomäki–Radziwiłł argument consumes; the logarithm here is the harmonic sum of
reciprocal separations, and removing it is exactly Montgomery–Vaughan's refinement of Hilbert's
inequality for the *Toeplitz* kernel `1/(m−n)`.  The corpus's `HilbertMatrixNormBound.lean` proves
`‖H‖ ≤ π` for the *Hankel* kernel `1/(m+n+1)` and does not supply it.  So this module is a genuine
milestone on the road to the external theorem, not a substitute for it.

### The sharp case — `Sieve/RootsOfUnityFrequencies.lean` (2026-08-03)

At the full set of `Q`-th roots of unity the elementary route already gives the *optimal* constant,
which is a check on the whole chain rather than a new estimate.

- `norm_eq_one_of_isPrimitiveRoot`, `norm_pow_eq_one_of_isPrimitiveRoot` — roots of unity and their
  powers are unimodular;
- `sum_range_pow_eq_zero` : a full geometric sum over a nontrivial root of unity vanishes;
- `ratio_ne_one` : distinct powers of a primitive root give a nontrivial ratio;
- **`inner_expRow_root_eq_zero`**, `inner_expRow_root_self` : the exponential rows of length `Q` at
  the `Q`-th roots of unity are *exactly orthogonal*, with diagonal exactly `Q`;
- `gram_row_root_eq` : hence every Gram row is exactly `Q`;
- **`largeSieve_roots`** : `‖∑_{j<Q} c_j φ_j‖² ≤ Q ∑_j |c_j|²`.

Built, wired, axiom-clean (seven theorems).  This is the sharp constant `N + δ^{-1}` at `N = Q`,
`δ = 1/Q`, with no logarithmic loss — `LargeSieveWeak.lean` specialises here to an equality-sharp
inequality, confirming that the loss in the general case is genuinely the harmonic sum of reciprocal
separations and not an artefact of the Gram-row argument.

### Lint gate

`scripts/formal_tools.py lint` reports **no** error attributable to any module added for these three
cards: every one is reachable from the `GaloisForLFunctions.RHTower` umbrella, with no `sorry`,
`axiom`, `opaque` or `unsafe` declaration and no build warning.  The nine errors the gate does
report are unwired modules owned by concurrent sessions in other areas.

### Arc versus chord — `Sieve/ChordalSeparation.lean` (2026-08-03)

The Gram-row bound is stated in the *chordal* separation `‖conj(ξ_r)ξ_t − 1‖`, whereas a sieve
hypothesis is normally an *arc* separation.  The conversion is now explicit:

- **`norm_exp_I_sub_one`** : `‖exp(iθ) − 1‖ = 2|sin(θ/2)|` — the chord subtended by an arc;
- **`four_mul_le_norm_exp_two_pi_I_sub_one`** : `4α ≤ ‖exp(2πiα) − 1‖` for `0 ≤ α ≤ 1/2`, by
  Jordan's inequality `sin t ≥ (2/π)t` on `[0, π/2]` (mathlib's `Real.mul_le_sin`).

Built, wired, axiom-clean.  So frequencies separated by `δ` in arc are separated by at least `4δ`
in chord, and the reciprocal separations in the Gram row are bounded accordingly.  This is the last
elementary conversion between the two ways of stating a large sieve hypothesis.

### Note on what is *not* being rebuilt

Mathlib already owns character orthogonality for finite abelian groups
(`Analysis/Fourier/FiniteAbelian/Orthogonality.lean`, in the weighted-inner-product `AddChar`
formalism) and a `ZMod` discrete Fourier transform.  `RootsOfUnityFrequencies.lean` is a
*specialisation* of that orthogonality to the corpus's own `expRow`/`EuclideanSpace` objects, which
is what the sieve chain consumes — not new mathematics, and no further Parseval layer will be built
on top of it.

### Bounded Dirichlet partial sums — `Sieve/DirichletKernelBound.lean` (2026-08-03)

First step of the route to the *sharp* large sieve constant.

- `exp_I_pow` : powers of `exp(iθ)` are the exponentials of the multiples of `θ`;
- **`norm_sum_exp_le`** : `‖∑_{d < D} exp(idθ)‖ ≤ 1/|sin(θ/2)|`, uniform in `D`;
- **`abs_sum_sin_le`** : `|∑_{d < D} sin(dθ)| ≤ 1/|sin(θ/2)|`.

Built, wired, axiom-clean.  The proof composes two corpus facts and adds nothing analytic: the
geometric sum bound `‖∑ ζ^d‖ ≤ 2/‖ζ − 1‖` of `GeometricSumBound.lean` with the chord identity
`‖exp(iθ) − 1‖ = 2|sin(θ/2)|` of `ChordalSeparation.lean`; taking imaginary parts loses nothing.

Uniformly bounded partial sums are the Abel-summation input for the classical estimate of
`∑_{d ≤ M} sin(dθ)/d`, which is what converts the Toeplitz kernel `1/(m−n)` into a *bounded* Fourier
multiplier.  That is the route to Hilbert's inequality, hence to replacing the current
`Δ = N + O(δ^{-1} log δ^{-1})` by `Δ = N + O(δ^{-1})` — the shape Matomäki–Radziwiłł consumes.

Recorded honestly: this route yields the sharp *shape* with some explicit constant, not the optimal
constant `π`, which needs the full infinite sawtooth series.  For the sieve application the shape is
what matters.

### Abel's inequality — `Sieve/AbelInequality.lean` (2026-08-03)

- **`abs_sum_mul_le_of_bounded_partial`** : if `|∑_{j<k} g j| ≤ B` for every `k`, and `w` is
  nonnegative and nonincreasing, then `|∑_{i<n} w i · g i| ≤ B · w 0`.

Built, wired, axiom-clean.  This is Dirichlet's test in quantitative form: summation by parts writes
the weighted sum as `w_{n-1}S_n` minus the increments `(w_{i+1} − w_i)S_{i+1}`, the increments are
nonpositive so their absolute values telescope to `w_0 − w_{n-1}`, and every partial sum is capped
by `B`.

Combined with `DirichletKernelBound.abs_sum_sin_le` (`|∑_{d<D} sin(dθ)| ≤ 1/|sin(θ/2)|`) and the
weight `w d = 1/(d+1)`, this is the estimate for `∑_{d ≤ M} sin(dθ)/d` that converts the Toeplitz
kernel `1/(m−n)` into a bounded Fourier multiplier — the remaining step to `Δ = N + O(δ^{-1})`.

### Abel on a tail — `Sieve/AbelTail.lean` (2026-08-03)

- `sum_range_shift` : shifted partial sums are differences of original ones;
- **`abs_sum_Ico_mul_le_of_bounded_partial`** : `|∑_{a ≤ i < n} w i · g i| ≤ 2B · w a`.
  Restricting to a tail costs only a factor two, and the bound carries the *weight at the cut*;
- **`abs_sum_sin_div_le`** : `|∑_{d < M} sin(dθ)/(d+1)| ≤ 1/|sin(θ/2)|`, by composing
  `DirichletKernelBound.abs_sum_sin_le` with `AbelInequality`.

Built, wired, axiom-clean.

**What is still missing, stated precisely.**  `abs_sum_sin_div_le` blows up as `θ → 0`, whereas the
true harmonic-weighted sine sum is bounded by an *absolute* constant.  The uniform bound needs the
range split at `a ≍ 1/|θ|`: below the cut `|sin(dθ)/(d+1)| ≤ |θ|` so that part is `≤ 1`; above it
`abs_sum_Ico_mul_le_of_bounded_partial` gives `2B/(a+1) ≍ 2|θ|/|sin(θ/2)| ≤ 2π`.  Both halves are
now available — the factor `w a` in the tail bound is exactly what makes the second half work — and
assembling them is the remaining step to a uniform constant, hence to `Δ = N + O(δ^{-1})`.

### Uniform harmonic sine bound — `Sieve/HarmonicSineBound.lean` (2026-08-03)

- **`abs_sum_sin_div_le_uniform`** :
  `|∑_{d < M} sin(dθ)/(d+1)| ≤ 1 + 3π`, uniformly in `M` and in `0 < θ ≤ π`.

Built, wired, axiom-clean.  This is the estimate the previous module said was still missing.  The
range is split at `⌈1/θ⌉`: below the cut each term satisfies `|sin(dθ)|/(d+1) ≤ dθ/(d+1) ≤ θ`, so
that half is at most `⌈1/θ⌉θ ≤ 1 + θ`; above it `AbelTail.abs_sum_Ico_mul_le_of_bounded_partial`
gives `2B/(⌈1/θ⌉+1) ≤ 2Bθ`, and Jordan's inequality caps `B = 1/|sin(θ/2)|` by `π/θ`, so that half
is at most `2π`.

The tail lemma's "weight at the cut" factor is exactly what makes the second half work: without it
the bound would degrade as `θ → 0`, which is precisely where the first half is longest.  The two
halves are therefore not interchangeable, and both were needed.

This is the Fourier multiplier bound for the Toeplitz kernel `1/(m−n)`: the kernel's symbol
`∑_{d} sin(dθ)/d` is bounded by an absolute constant, which is what Hilbert's inequality asserts.
Converting it into the bilinear statement `|∑_{m≠n} x_m x̄_n/(m−n)| ≤ C ∑|x_n|²` — and hence into
`Δ = N + O(δ^{-1})` — is the remaining step.

### Next step scoped: exact discrete Parseval (2026-08-03)

`HarmonicSineBound.abs_sum_sin_div_le_uniform` bounds the *symbol* of the Toeplitz kernel.  Turning
that into the bilinear Hilbert inequality `|∑_{m≠n} x_m x̄_n/(m−n)| ≤ C ∑|x_n|²` needs one more
identity, and it is now precisely located:

    (1/Q) ∑_{j<Q} |⟪expRow Q (ζ^j), x⟫|² = ‖x‖²      (exact discrete Parseval)

`RootsOfUnityFrequencies.lean` already gives the two inputs — the family `expRow Q (ζ^j)` is
pairwise orthogonal with every diagonal entry exactly `Q`.  What remains is to promote `Q` pairwise
orthogonal vectors of norm² `Q` in a `Q`-dimensional space to an orthonormal *basis* and read off
Parseval.  API established for this toolchain:

- `finrank_euclideanSpace_fin : finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n`;
- `basisOfOrthonormalOfCardEqFinrank : Orthonormal 𝕜 v → Fintype.card ι = finrank 𝕜 E → Basis ι 𝕜 E`;
- `OrthonormalBasis.mk : Orthonormal 𝕜 v → ⊤ ≤ span 𝕜 (range v) → OrthonormalBasis ι 𝕜 E`;
- Parseval is `OrthonormalBasis.sum_inner_mul_inner` at `y = x`, since
  `⟪x, b i⟫⟪b i, x⟫ = |⟪b i, x⟫|²`.

Names that do **not** exist here (checked, so they are not retried): `OrthonormalBasis.sum_sq_norm_inner`,
`OrthonormalBasis.norm_sq_eq_sum`, `OrthonormalBasis.sum_norm_sq_inner`.

Note the scale: the family has norm² `Q`, not `1`, so the orthonormal family is `Q^{-1/2} • expRow`,
and the `1/Q` in the Parseval statement is that normalisation — not a convention.

### Exact discrete Parseval landed — `Sieve/DiscreteParseval.lean` (2026-08-03)

The identity scoped in the previous entry is now proved.

- `unitRow Q ζ j := Q^{-1/2} • expRow Q (ζ^j)`;
- `orthonormal_unitRow` : the rescaled rows are orthonormal;
- `span_unitRow`, `rootBasis`, `rootBasis_apply` : `Q` orthonormal vectors in a `Q`-dimensional
  space form an orthonormal basis;
- **`sum_norm_inner_expRow_root`** :
  `∑_{j < Q} |⟪expRow Q (ζ^j), x⟫|² = Q ‖x‖²`.

Built, wired, axiom-clean (four theorems).  Parseval is `OrthonormalBasis.sum_inner_mul_inner` at
`y = x`, using `⟪x, b j⟫⟪b j, x⟫ = |⟪b j, x⟫|²`; the factor `Q` is the rescaling, since the
unnormalised rows have squared norm `Q`.

With this and `HarmonicSineBound.abs_sum_sin_div_le_uniform` both unconditional, the two halves of
the Toeplitz argument are in place: the symbol of `1/(m−n)` is bounded by an absolute constant, and
the quadratic form is an exact average of that symbol against `|∑ x_n ζ^{jn}|²` which Parseval
returns to `∑|x_n|²`.  Assembling them into
`|∑_{m≠n} x_m x̄_n/(m−n)| ≤ C ∑|x_n|²` — and hence `Δ = N + O(δ^{-1})` — is the remaining step.

### Bounded symbol gives bounded form — `Sieve/SymbolBound.lean` (2026-08-03)

- **`abs_sum_symbol_mul_norm_inner_le`** :
  `|∑_j c_j |⟪expRow Q (ζ^j), x⟫|²| ≤ C · Q ‖x‖²` whenever `|c_j| ≤ C`.

Built, wired, axiom-clean.  Triangle inequality followed by exact discrete Parseval; no cancellation
is used, so the constant is exactly the sup-norm of the symbol.

This is the abstract half of Hilbert's inequality, and it now sits directly on top of the concrete
half: `HarmonicSineBound.abs_sum_sin_div_le_uniform` bounds the symbol of the Toeplitz kernel
`1/(m−n)` by an absolute constant.

**What remains is one identification, stated precisely.**  To apply the above to that kernel one
must exhibit the quadratic form `∑_{m≠n} x_m x̄_n/(m−n)` as `(1/Q)∑_j c_j |⟪expRow Q (ζ^j), x⟫|²`
with `c_j` the kernel's symbol at `ζ^j`.  That is the finite convolution identity — an exact
computation using the same roots-of-unity orthogonality already in
`RootsOfUnityFrequencies.lean`, valid once `Q` exceeds twice the support length so that no
wraparound occurs.  It is bookkeeping over an established orthogonality relation, not a new
estimate.

### Coefficient expansion — `Sieve/CoefficientExpansion.lean` (2026-08-03)

- **`inner_expRow_apply`** : `⟪expRow Q ξ, x⟫ = ∑_m conj(ξ^m) x_m` — the coefficient is the finite
  Fourier coefficient;
- **`normSq_inner_expRow`** :
  `|⟪expRow Q ξ, x⟫|² = ∑_m ∑_n (conj(ξ^m) x_m) · conj(conj(ξ^n) x_n)`.

Built, wired, axiom-clean.  Both are exact and use *no* orthogonality — the first is the definition
of the inner product on `EuclideanSpace`, the second is `|z|² = z·conj z` with the sum expanded.

**Remaining bookkeeping, stated exactly.**  Summing `normSq_inner_expRow` against a symbol `c_j` and
exchanging the order of summation gives

    ∑_j c_j |⟪expRow Q (ζ^j), x⟫|² = ∑_m ∑_n x_m conj(x_n) · (∑_j c_j conj(ζ^{jm}) ζ^{jn}),

so the multiplier with symbol `c` *is* the kernel `Ǩ(m,n) = ∑_j c_j ζ^{j(n−m)}`.  Identifying that
kernel with `1/(m−n)` — for `Q` past twice the support length, via the roots-of-unity orthogonality
of `RootsOfUnityFrequencies.lean` — then combines with `SymbolBound.lean` and
`HarmonicSineBound.lean` to give `|∑_{m≠n} x_m x̄_n/(m−n)| ≤ C ∑|x_n|²`.

Every ingredient of that chain is now unconditional in the corpus; what is left is index
manipulation over identities already proved, with no further estimate required.

### Multiplier is a kernel — `Sieve/CoefficientExpansion.lean`, second theorem (2026-08-03)

- **`sum_symbol_mul_normSq_eq`** :
  `∑_j c_j |⟪expRow Q (ζ^j), x⟫|² = ∑_m ∑_n x_m conj(x_n) · (∑_j c_j conj(ζ^{jm}) ζ^{jn})`.

Built, wired, axiom-clean.  This is the bookkeeping step flagged in the previous entry, now proved:
summing the coefficient expansion against a symbol and exchanging the order of summation exhibits
the Fourier multiplier with symbol `c` as the kernel `Ǩ(m,n) = ∑_j c_j ζ^{j(n−m)}`.  Exact — no
orthogonality, no estimate.

**Status of the Toeplitz argument.**  Every analytic ingredient is unconditional in the corpus:

| step | module |
|-|-|
| symbol of `1/(m−n)` is bounded by an absolute constant | `HarmonicSineBound.lean` |
| bounded symbol ⟹ bounded quadratic form | `SymbolBound.lean` |
| exact discrete Parseval | `DiscreteParseval.lean` |
| multiplier ⟹ kernel | `CoefficientExpansion.lean` |
| roots-of-unity orthogonality | `RootsOfUnityFrequencies.lean` |

What remains is to run the kernel identification in the one direction not yet written out: choosing
`c_j` as the partial sums of `1/d` against `ζ^{jd}` and checking, via the orthogonality above, that
`Ǩ(m,n) = 1/(m−n)` once `Q` exceeds twice the support length.  That is a choice of `c` plus an
orthogonality computation over identities already proved.

### Orthogonality in divisibility form — `Sieve/RootOrthogonality.lean` (2026-08-03)

- **`sum_pow_mul_eq`** : `∑_{j < Q} (ζ^k)^j = Q` if `Q ∣ k`, else `0`;
- `sum_pow_mul_index_eq` : the same with the exponent written `ζ^{jk}`, the form it takes after
  exchanging summation order.

Built, wired, axiom-clean.  Stating the relation with an `if` on `Q ∣ k` — rather than as two
separate lemmas — is what makes it usable as a *rewrite inside a sum over `k`*, which is exactly what
the inverse discrete Fourier transform needs: summing a symbol against `ζ^{jk}` and exchanging
returns the coefficient at the surviving index.

Note both theorems hold without any positivity hypothesis on `Q`; the `0 < Q` I first assumed turned
out to be unnecessary, so the statements are the general ones.

With `CoefficientExpansion.sum_symbol_mul_normSq_eq` this closes the multiplier/kernel dictionary in
both directions: a symbol determines its kernel, and orthogonality recovers the symbol's
coefficients from it.

### Kernel recovery — `Sieve/InverseDFT.lean` (2026-08-03)

- **`kernel_of_symbol`** :
  `∑_j (∑_d K_d ζ^{jd}) ζ^{jk} = Q · ∑_{d : Q ∣ d + k} K_d`.

Built, wired, axiom-clean.  One exchange of summation followed by the divisibility form of
orthogonality; the `if` in `RootOrthogonality.sum_pow_mul_eq` collapses the inner sum to the
surviving residue class.  When `K` is supported on `range Q` the congruence pins down a single `d`,
so the right-hand side is `Q · K_{(−k) mod Q}` — the inverse discrete Fourier transform.

That is the reason the orthogonality lemma was stated with an `if` rather than as two branches: the
`if` is what survives the exchange and becomes the filter on the right.

The multiplier/kernel dictionary is now complete and unconditional in both directions —
`CoefficientExpansion.sum_symbol_mul_normSq_eq` sends a symbol to its kernel, `kernel_of_symbol`
recovers the coefficients — alongside the bounded-symbol bound (`SymbolBound`), exact Parseval
(`DiscreteParseval`), and the absolute bound on the symbol of `1/(m−n)` (`HarmonicSineBound`).

### Inverse DFT completed — `Sieve/ResidueSingleton.lean` (2026-08-03)

- `filter_dvd_add_eq` : for `k < Q` the surviving residue class `{d < Q : Q ∣ d + k}` is the
  singleton `{(Q − k) % Q}` — since `d + k < 2Q`, the only multiples of `Q` it can equal are `0`
  and `Q`;
- `sum_filter_dvd_add` : hence the filtered sum is a single coefficient;
- **`kernel_of_symbol_singleton`** :
  `∑_j (∑_d K_d ζ^{jd}) ζ^{jk} = Q · K_{(Q−k) % Q}`.

Built, wired, axiom-clean.  The `(Q − k) % Q` form covers both branches uniformly: it is `0` when
`k = 0` and `Q − k` otherwise, so no case split leaks into the statement.

This completes the inverse discrete Fourier transform.  Every component of the Toeplitz argument now
exists unconditionally in the corpus:

| step | module |
|-|-|
| symbol of `1/(m−n)` bounded absolutely | `HarmonicSineBound.lean` |
| bounded symbol ⟹ bounded quadratic form | `SymbolBound.lean` |
| exact discrete Parseval | `DiscreteParseval.lean` |
| symbol ⟹ kernel | `CoefficientExpansion.lean` |
| kernel ⟹ coefficients (inverse DFT) | `RootOrthogonality.lean`, `InverseDFT.lean`, `ResidueSingleton.lean` |

What remains is to choose the coefficient sequence `K_d` matching `1/d` on the relevant range and
read the bilinear inequality off the dictionary — an instantiation, with every supporting identity
and estimate already proved.

### Bilinear bound on the kernel side — `Sieve/BilinearMultiplier.lean` (2026-08-03)

- **`abs_sum_kernel_bilinear_le`** :
  `‖∑_m ∑_n x_m conj(x_n) Ǩ(m,n)‖ ≤ C · Q ‖x‖²` for `Ǩ(m,n) = ∑_j c_j conj(ζ^{jm}) ζ^{jn}`
  and any real symbol with `|c_j| ≤ C`.

Built, wired, axiom-clean.  This is Hilbert's inequality in its structural form: the left side is an
arbitrary sesquilinear form built from a Toeplitz-type kernel, and the bound depends only on the
sup-norm of that kernel's symbol.  No property of the particular kernel enters.

The whole multiplier apparatus is now closed.  Specialising to `1/(m−n)` means choosing the
coefficient sequence and invoking `HarmonicSineBound.abs_sum_sin_div_le_uniform` for its symbol —
the one remaining instantiation, with every identity and estimate it needs already proved.

### Matching the two kernel shapes — `Sieve/KernelReshape.lean` (2026-08-03)

The multiplier side produces the kernel as `∑_j c_j conj(ζ^{jm}) ζ^{jn}`; the inverse transform
consumes it as `∑_j c_j ζ^{jk}`.  The bridge is that conjugation is inversion on the unit circle.

- **`conj_pow_eq`** : `conj(ζ^{jm}) = ζ^{j(Q−m)}` for `m ≤ Q` — both sides are inverses of `ζ^{jm}`,
  the first because `|ζ| = 1`, the second because `ζ^{j(Q−m)}ζ^{jm} = (ζ^Q)^j = 1`;
- **`kernel_pairing_eq`** : substituting turns the conjugate pairing into the single character
  `ζ^{j((Q−m)+n)}`.

Built, wired, axiom-clean.  `(Q−m)+n` is precisely the index at which
`ResidueSingleton.kernel_of_symbol_singleton` reads off a coefficient, so the two halves of the
dictionary now compose without any remaining shape mismatch.

### Kernel of a transform symbol — `Sieve/KernelValue.lean` (2026-08-03)

- **`kernel_value`** : for `n < m < Q`,
  `∑_j (∑_d K_d ζ^{jd}) conj(ζ^{jm}) ζ^{jn} = Q · K_{m−n}`.

Built, wired, axiom-clean.  This is the two halves of the dictionary composed into one statement:
`KernelReshape.conj_pow_eq` turns the conjugate pairing into the character `ζ^{j((Q−m)+n)}`, and
`ResidueSingleton.kernel_of_symbol_singleton` reads off the coefficient at
`(Q − ((Q−m)+n)) % Q`, which for `n < m < Q` is exactly `m − n`.

Restricting to the strict lower triangle `n < m` is not a loss: a Toeplitz kernel is determined off
the diagonal by its lower triangle together with its symmetry type.  The bound `m < Q` excludes only
the degenerate corner `m = Q, n = 0`, where the residue would wrap.

A symbol built from coefficients therefore *has* those coefficients as its kernel, with the factor
`Q` of the transform.  Together with `BilinearMultiplier.abs_sum_kernel_bilinear_le` — which bounds
any such bilinear form by the sup-norm of the symbol — the apparatus is complete: prescribing `K_d`
and bounding the resulting symbol gives a bilinear inequality for that kernel.

### Why the kernel must be antisymmetric — `Sieve/AntisymmetricSymbol.lean` (2026-08-03)

- **`antisym_pow_eq`** : `ζ^{jd} − ζ^{j(Q−d)} = 2i · Im(ζ^{jd})`, since the second term is the
  conjugate of the first;
- **`antisym_symbol_eq`** : hence the antisymmetrised symbol of a real coefficient sequence is `2i`
  times a real sine sum.

Built, wired, axiom-clean.

This records a structural point that the earlier entries left implicit and that would otherwise be
easy to get wrong.  The *full* symbol of a one-sided sequence `K_d = 1/d` is **not** bounded: its
real part is `∑_d cos(dθ)/d`, which diverges like `−log|2 sin(θ/2)|`.  Only the imaginary part is
uniformly bounded.  That is precisely why Hilbert's inequality concerns `1/(m−n)` — an
*antisymmetric* kernel — and not `1/|m−n|`, and it is why `HarmonicSineBound.lean` bounds a **sine**
sum rather than a full exponential sum.

So the coefficient sequence to feed into `KernelValue.kernel_value` is the antisymmetric one, whose
symbol is `2i` times the quantity already bounded by `1 + 3π`.

### Symbol's imaginary part is the sine sum — `Sieve/SymbolImaginaryPart.lean` (2026-08-03)

- `im_exp_pow` : `Im((exp(iθ))^k) = sin(kθ)`;
- **`abs_sum_im_exp_pow_div_le`** :
  `|∑_{d < M} Im((exp(iθ))^d)/(d+1)| ≤ 1 + 3π`, uniformly in `M` and `0 < θ ≤ π`.

Built, wired, axiom-clean.  The multiplier apparatus produces the antisymmetrised symbol as `2i`
times `∑_d K_d Im(ζ^{jd})`, whereas `HarmonicSineBound.lean` bounds a sum of `Real.sin`; this
identifies the two, so the uniform bound now sits directly on the quantity the kernel dictionary
consumes rather than on a paraphrase of it.

Every piece of the Hilbert-inequality argument is now expressed in the *same* vocabulary — powers of
a root of unity, their imaginary parts, and the kernel dictionary — with no remaining translation
step between the analytic estimate and the algebraic apparatus.

### The concrete root and its angles — `Sieve/ConcreteRoot.lean` (2026-08-03)

Everything above was stated for an abstract primitive root.  Instantiating at `ζ = exp(2πi/Q)` makes
the angles explicit.

- `rootOfUnity Q`, `rootOfUnity_pow` : `ζ^j = exp(iθ_j)` with `θ_j = 2πj/Q`;
- `isPrimitiveRoot_rootOfUnity` : it is primitive (mathlib's `Complex.isPrimitiveRoot_exp`, modulo
  moving the cast);
- **`abs_sum_im_rootOfUnity_pow_div_le`** : for `1 ≤ j` and `2j ≤ Q`,
  `|∑_{d < M} Im((ζ^j)^d)/(d+1)| ≤ 1 + 3π`.

Built, wired, axiom-clean.  The hypothesis range `1 ≤ j`, `2j ≤ Q` is exactly `0 < θ_j ≤ π`, which is
where the harmonic sine bound holds; it is the natural half of the frequencies, and no generality is
lost, because the symbol at `j` and at `Q − j` are conjugate.

The symbol bound is now available at a concrete root of unity, so the abstract apparatus
(`KernelValue`, `BilinearMultiplier`) can be instantiated without carrying an abstract `ζ` and a
separate hypothesis that its symbol is bounded.

### Symbol bound at every frequency — `Sieve/SymbolReflection.lean` (2026-08-03)

- `im_pow_reflect` : `Im((ζ^{Q−j})^d) = −Im((ζ^j)^d)`, since `ζ^{Q−j}` is the conjugate of `ζ^j`;
- **`abs_sum_im_rootOfUnity_pow_div_le_all`** : the uniform bound `1 + 3π` holds at *every*
  frequency `j < Q`.

Built, wired, axiom-clean.  The previous entry bounded the symbol only on the half range
`1 ≤ j`, `2j ≤ Q`.  The remaining frequencies need no new estimate: `j = 0` gives the zero symbol
because every power of `1` is real, and `j > Q/2` reflects to `Q − j` in the half range with the
symbol negated.

This matters because `BilinearMultiplier.abs_sum_kernel_bilinear_le` quantifies over *all*
`j : Fin Q` — a bound on half the frequencies would not have satisfied its hypothesis.  The symbol
bound is now in exactly the shape that theorem consumes.

### Hilbert's inequality, bilinear form — `Sieve/HilbertBilinear.lean` (2026-08-03)

- `hilbertSymbol Q M j := ∑_{d < M} Im((ζ^j)^d)/(d+1)` at the standard `Q`-th root of unity;
- `abs_hilbertSymbol_le` : bounded by `1 + 3π` at every frequency;
- **`hilbert_bilinear_bound`** :
  `‖∑_m ∑_n x_m conj(x_n) Ǩ(m,n)‖ ≤ (1 + 3π) · Q ‖x‖²`

  for the kernel `Ǩ` that symbol generates, with an absolute constant, uniformly in `Q`, `M`
  and `x`.

Built, wired, axiom-clean.  This is Hilbert's inequality in the corpus's formulation: an
antisymmetric Toeplitz kernel with harmonic coefficients has bilinear form controlled by the energy,
with no dependence on the length.

The constant is `1 + 3π`, not the optimal `π`; as recorded when the symbol bound was built, the
optimal constant requires the full infinite sawtooth series, and for the sieve application only the
*shape* matters.

Chain, all unconditional and each proved in this corpus:

    GeometricSumBound → DirichletKernelBound → AbelInequality → AbelTail → HarmonicSineBound
      → SymbolImaginaryPart → ConcreteRoot → SymbolReflection ─┐
    RootsOfUnityFrequencies → DiscreteParseval → SymbolBound ──┤
    CoefficientExpansion → KernelReshape ──────────────────────┴→ BilinearMultiplier
                                                                    → HilbertBilinear

### Correction: what the corpus's Hilbert inequality does and does not give (2026-08-03)

The previous entry closed with "next: use this to upgrade `Δ = N + O(δ^{-1} log δ^{-1})` to
`Δ = N + O(δ^{-1})`".  Traced through, **that step is not available from what is proved**, and the
claim is withdrawn.

`HilbertBilinear.hilbert_bilinear_bound` is the inequality for the kernel generated by a symbol *at
the `Q`-th roots of unity* — that is, for frequencies `λ_r = r/Q` which are **equally spaced**.  The
Montgomery–Vaughan route to the sharp large sieve constant needs Hilbert's inequality for
**arbitrary well-spaced** real frequencies `λ_1 < … < λ_R` with `λ_{r+1} − λ_r ≥ δ`:

    |∑_{r ≠ s} x_r conj(x_s) / (λ_r − λ_s)| ≤ π δ^{-1} ∑ |x_r|²

That generalisation is the actual content of Montgomery–Vaughan (1974); its proof is a different and
harder argument, not a corollary of the cyclic case.  In the equally-spaced case the corpus already
had the sharp constant directly, from exact orthogonality
(`RootsOfUnityFrequencies.largeSieve_roots`), so the cyclic Hilbert inequality does not improve the
general bound.

**Accordingly, the status is unchanged from before this sub-programme**: the corpus owns the *weak*
large sieve `Δ = N + O(δ^{-1} log δ^{-1})` (`LargeSieveWeak.lean`), and the sharp `Δ = N + δ^{-1}`
remains open, now with its obstruction identified precisely as the well-spaced generalisation rather
than as "Hilbert's inequality" unqualified.

What the sub-programme did produce, all unconditional and none of it in mathlib: the geometric and
Dirichlet-kernel bounds, Abel's inequality in plain and tail form, the uniform harmonic sine bound,
exact discrete Parseval, the multiplier/kernel dictionary in both directions, and the cyclic Hilbert
inequality.  Those are reusable regardless, and the last of them is the equally-spaced case of the
theorem still needed.

### Separated points spread linearly — `Sieve/SeparatedPoints.lean` (2026-08-03)

- **`le_of_gap`** : if consecutive gaps are at least `δ` then `λ_r + (s−r)δ ≤ λ_s` for `r ≤ s`;
- `inv_dist_le` : hence `|λ_r − λ_s|^{-1} ≤ ((s−r)δ)^{-1}`.

Built, wired, axiom-clean.  This is the telescoping that converts a *separation* hypothesis into the
reciprocal bounds appearing in a Gram row, and it is stated for real frequencies rather than for
unimodular ratios, so it applies to the general (non-cyclic) setting.

It also makes the source of the logarithmic loss explicit and unavoidable for any absolute-values
argument: summing `((s−r)δ)^{-1}` over `s ≠ r` gives `2δ^{-1}H_{R−1} ≍ δ^{-1} log R`.  Montgomery–
Vaughan's sharp constant is obtained by exploiting *cancellation* in `∑_{r≠s} x_r x̄_s/(λ_r−λ_s)`
rather than bounding term by term — which is why, as recorded in the correction above, the cyclic
Hilbert inequality does not supply it.

### Formal layer — the Gram row of a separated family is harmonic

`formal/GaloisForLFunctions/RHTower/Sieve/SeparatedRowSum.lean` completes the separation estimate of
`SeparatedPoints.lean` into a full row bound. For real frequencies with consecutive gaps at least
`δ > 0` and any `r < R`:

- `lt_of_gap` — separated points are strictly increasing.
- `sum_inv_dist_le` — `∑_{r < s < R} (λ_s − λ_r)^{-1} ≤ δ^{-1} ∑_{i < R−r−1} (i+1)^{-1}`.
- `sum_inv_dist_below_le` — the same bound below `r`, obtained by reflecting the range rather than
  by a second estimate.
- `sum_inv_abs_dist_le` — `∑_{s ≠ r, s < R} |λ_s − λ_r|^{-1} ≤ 2 δ^{-1} ∑_{i < R} (i+1)^{-1}`.

All four are unconditional (`[propext, Classical.choice, Quot.sound]`).

Consequence for the route: the harmonic sum on the right is *exactly* the loss incurred by any
argument that bounds `∑_{r ≠ s} x_r conj(x_s)(λ_r − λ_s)^{-1}` term by term — including the Gram-row
route used in `LargeSieveWeak.lean`. So the weak large sieve's `Δ = N + O(δ^{-1} log R)` is not an
artefact of that particular assembly; it is the ceiling of the whole absolute-value method, now a
theorem rather than an observation. Montgomery–Vaughan's sharp `Δ = N + δ^{-1}` must therefore come
from cancellation inside that sum. The cyclic Hilbert inequality already in the corpus
(`HilbertBilinear.lean`) supplies cancellation only for equally spaced frequencies, where
`largeSieve_roots` already gives the sharp constant by orthogonality; it does not extend to the
arbitrary well-spaced case, which remains the open input.

### Formal layer — the chord bound on the circle

The separation estimates above are stated for real frequencies, but a sieve hypothesis separates
frequencies in `ℝ/ℤ`. Two modules supply the missing conversion, both unconditional.

`formal/GaloisForLFunctions/RHTower/Sieve/CircleSeparation.lean`:

- `mul_abs_le_abs_sin` — Jordan's inequality made two-sided: `(2/π)|x| ≤ |sin x|` for `|x| ≤ π/2`.
- `four_mul_abs_le_norm_exp_two_pi` — `4|β| ≤ ‖e(β) − 1‖` for `|β| ≤ 1/2`.
- `exp_two_pi_sub_round` — reducing the argument of `e(·)` modulo one changes nothing.
- `four_mul_round_dist_le` — `4|α − round α| ≤ ‖e(α) − 1‖` at *every* real `α`.

`formal/GaloisForLFunctions/RHTower/Sieve/CircleDistance.lean` names the distance to the nearest
integer `toIntDist x = |x − round x|` and proves what a separation count needs: it is at most `1/2`,
it is invariant under integer shifts (`toIntDist_add_int`), it agrees with `|x|` when `|x| < 1/2`
(`toIntDist_eq_abs_of_abs_lt_half`, via `round_eq_zero_of_abs_lt_half`), and — the form the counting
uses — `toIntDist_sub_lt`: if the reduced representatives of `u` and `v` lie within `δ ≤ 1/2` of each
other then `u` and `v` lie within `δ` on the circle. `four_mul_toIntDist_le` restates the chord bound
in these terms.

`toIntDist_sub_lt` is the lemma that converts "two points in a short arc" into "two points violating
the separation hypothesis", which is the step the circle row-sum needs and the reason the real-line
estimate `sum_inv_abs_dist_le` does not transfer directly: on the circle the ordering of the
frequencies does not bound their distances, only their reduced offsets do.

### Formal layer — the large sieve with an explicit Δ

Two further modules close the gap between the abstract Bessel inequality of `LargeSieveWeak.lean`
and a usable sieve statement. Both unconditional.

`formal/GaloisForLFunctions/RHTower/Sieve/CircleRowSum.lean` proves the Gram row of a family
`δ`-separated in `ℝ/ℤ` is harmonic:

`circle_row_sum_le` — `∑_{t ≠ r} ‖λ_t − λ_r‖^{-1} ≤ 2δ^{-1} ∑_{1 ≤ k ≤ M} k^{-1}` for `M ≥ (2δ)^{-1}`,

together with `one_le_levelOf`, `levelOf_mul_le`, `lt_levelOf_succ_mul`, `levelOf_le`. The index
ordering is *not* available here — on the circle the frequencies may wrap — so the count is by band:
each `λ_t − λ_r` reduces to an offset in `[−1/2, 1/2]` lying in some `[kδ, (k+1)δ)`; two frequencies
in the same band on the same side of zero have offsets differing by less than `δ` and so violate the
separation hypothesis (`toIntDist_sub_lt`). Hence the level–side pair is injective, at most two
frequencies per level, and no level exceeds `(2δ)^{-1}` since offsets never exceed `1/2`.

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveSeparated.lean` assembles this with the chord
bound:

- `circleFreq`, `norm_circleFreq`, `conj_circleFreq_mul` — the correlation of two circle frequencies
  is the frequency of their difference.
- `four_mul_toIntDist_le_norm_sub` — chordal separation from circle separation.
- `largeSieve_separated` — **`∑_r |⟪e(λ_r), a⟫|² ≤ (N + δ^{-1} ∑_{1 ≤ k ≤ M} k^{-1}) ‖a‖²`** for
  `λ` pairwise `δ`-separated in `ℝ/ℤ` and `M ≥ (2δ)^{-1}`.

This is the first statement in the corpus where the large sieve constant is *computed* from a
separation hypothesis rather than assumed: `Δ = N + O(δ^{-1} log δ^{-1})`, everything explicit. The
sharp `Δ = N + δ^{-1}` is a different theorem — `sum_inv_abs_dist_le` shows the harmonic factor is
the provable ceiling of the absolute-value method, so removing it requires cancellation
(Montgomery–Vaughan), not a better assembly of these pieces.

### Formal layer — the large sieve constant in closed form

`formal/GaloisForLFunctions/RHTower/Sieve/HarmonicLogBound.lean` identifies the partial harmonic
sums produced by the Gram-row estimates with mathlib's harmonic numbers and quotes the logarithmic
bound: `sum_Icc_one_div_eq_sum_range`, `sum_Icc_one_div_eq_harmonic`, and
`sum_Icc_one_div_le_one_add_log` (`∑_{1 ≤ k ≤ M} k^{-1} = H_M ≤ 1 + log M`).

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveExplicit.lean` removes the free cut:

- `largeSieve_separated_log` — `Δ = N + δ^{-1}(1 + log M)` for any `M ≥ (2δ)^{-1}`.
- `largeSieve_separated_explicit` — **`∑_r |⟪e(λ_r), a⟫|² ≤ (N + δ^{-1}(1 + log((2δ)^{-1}+1))) ‖a‖²`**
  for any family `δ`-separated in `ℝ/ℤ`, taking `M = ⌈(2δ)^{-1}⌉`.

Both unconditional. This is the weak large sieve in closed form: no free parameter, no hypothesis
beyond the separation, and `Δ = N + O(δ^{-1} log δ^{-1})` now written out rather than described.

Status of the route's sieve layer: the weak large sieve is complete and usable. What is *not* here
is the sharp `Δ = N + δ^{-1}`; `sum_inv_abs_dist_le` proves the logarithm is the ceiling of the
absolute-value method, so it can only be removed by Montgomery–Vaughan's cancellation argument for
arbitrary well-spaced frequencies, which remains the open input alongside Matomäki–Radziwiłł.

### Formal layer — the arithmetic large sieve

`formal/GaloisForLFunctions/RHTower/Sieve/FareySeparation.lean`:

- `one_div_le_toIntDist_of_not_dvd` — a rational with denominator `D` is either an integer or at
  distance at least `D^{-1}` from every integer. Writing `m/D − round(m/D) = (m − D·round(m/D))/D`,
  the numerator is an integer that vanishes exactly when `D ∣ m`.
- `one_div_le_toIntDist_farey` — hence `‖a/q − a'/q'‖ ≥ (qq')^{-1}` whenever the two fractions are
  distinct modulo one.

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveFarey.lean`:

- `largeSieve_farey` — **`∑ |⟪e(a_i/q_i), x⟫|² ≤ (N + Q²(1 + log(Q²/2 + 1))) ‖x‖²`** for rationals
  with denominators at most `Q ≥ 2`, pairwise distinct modulo one.

Both unconditional. This is the arithmetic shape of the large sieve — the form an actual sieve
application consumes — obtained by feeding Farey separation (`δ = Q^{-2}`) into the closed-form
statement. The classical constant is `N + Q²`; the surplus logarithmic factor is exactly the one
`sum_inv_abs_dist_le` proves the absolute-value method cannot avoid, so closing the gap to the
classical constant is Montgomery–Vaughan's theorem and not a rearrangement of these steps.

### Formal layer — the large sieve on the Farey set

`formal/GaloisForLFunctions/RHTower/Sieve/FareyCoprime.lean` discharges the last hypothesis.

- `not_dvd_farey_cross` — distinct reduced fractions in the standard range are automatically
  distinct modulo one. If `qq' ∣ aq' − a'q` with `(a,q) = (a',q') = 1`, then `q ∣ aq'` forces
  `q ∣ q'` and symmetrically `q' ∣ q`, so `q = q'`; cancelling gives `q ∣ a − a'`, and `1 ≤ a,a' ≤ q`
  leaves `a = a'`.
- `largeSieve_farey_reduced` — **`∑_{(a,q)} |⟪e(a/q), x⟫|² ≤ (N + Q²(1 + log(Q²/2+1))) ‖x‖²`** over
  any set of pairs with `0 < q ≤ Q`, `1 ≤ a ≤ q`, `gcd(a,q) = 1`, and `Q ≥ 2`.

Both unconditional. The sieve hypothesis is now membership in the Farey set of order `Q` and nothing
else — the arithmetic input (coprimality) has replaced the analytic one (separation), which is the
form in which the large sieve is actually invoked.

### Formal layer — the large sieve for exponential sums

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveExpSum.lean` puts the chain into the shape the
sieve is actually invoked in. With `S(θ) = ∑_{n<N} c_n e(nθ)` (`expSum`):

- `norm_inner_expRow_conjVec` — the exponential coefficient `⟪expRow N e(θ), ·⟫` *is* `S(θ)` when
  read at the conjugated coefficient vector (`conjVec`).
- `norm_sq_conjVec` — that vector's energy is `∑_n |c_n|²`.
- `largeSieve_expSum_farey` — **`∑_{(a,q)} |S(a/q)|² ≤ (N + Q²(1 + log(Q²/2+1))) ∑_n |c_n|²`** over
  the Farey set of order `Q ≥ 2`.

All unconditional. This is the classical statement of the large sieve up to the logarithmic factor,
now with no inner-product formulation left in the way: coefficients in, exponential-sum bound out.

### Formal layer — the large sieve in textbook form

`formal/GaloisForLFunctions/RHTower/Sieve/FareySet.lean` supplies the canonical instance and the
familiar shape:

- `fareySet Q`, `mem_fareySet` — the Farey set of order `Q` (reduced `a/q` with `1 ≤ a ≤ q ≤ Q`).
- `largeSieve_expSum_fareySet` — the large sieve on it, hypothesis-free.
- `fareySet_eq_biUnion` — the Farey set fibred over its denominators; the fibres are disjoint
  because the second coordinate determines the denominator.
- `largeSieve_expSum_double` — **`∑_{q ≤ Q} ∑_{1 ≤ a ≤ q, (a,q)=1} |S(a/q)|² ≤
  (N + Q²(1 + log(Q²/2+1))) ∑_n |c_n|²`**.

All unconditional. The route's large-sieve input is now available in exactly the form applications
quote it, with `Q ≥ 2` the only hypothesis.

### Formal layer — the dual large sieve

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveDual.lean` supplies the bilinear (dual) half,
which is the shape a Halász–Montgomery argument consumes.

- `circleFreq_corr_ne_one`, `circleFreq_row_le` — the two ingredients (nontrivial correlations, the
  Gram row bound) isolated so both the Bessel and bilinear forms rest on the same statements.
- `largeSieve_separated_bilinear` — `‖∑_r c_r e(λ_r)‖² ≤ (N + δ^{-1}(1 + log((2δ)^{-1}+1))) ∑_r |c_r|²`
  for frequencies `δ`-separated in `ℝ/ℤ`.
- `norm_sq_sum_smul_expRow` — the same quantity in coordinates: a mean square over `n < N`.
- `fareySet_sep` — Farey fractions of order `Q` are `Q^{-2}`-separated (no hypothesis on `Q`; for
  `Q ≤ 1` the statement is vacuous because no two distinct points exist).
- `largeSieve_dual_fareySet` — **`∑_{n<N} |∑_{(a,q)} b_{a,q} e(na/q)|² ≤
  (N + Q²(1 + log(Q²/2+1))) ∑ |b|²`**.

All unconditional. The large sieve is now available in both directions with the same explicit
constant, so downstream arguments can use whichever pairing they need.

### Formal layer — exponential sums depend only on residues

`formal/GaloisForLFunctions/RHTower/Sieve/ResidueSum.lean` is the entry point that lets a sieve
hypothesis about residue classes reach the large sieve.

- `circleFreq_add_int` — `e(·)` is invariant under integer translation.
- `circleFreq_div_eq_rootOfUnity_pow` — `e(m/q)` is the `m`-th power of the standard `q`-th root of
  unity, linking this layer to the orthogonality already in `RootOrthogonality.lean`.
- `circleFreq_mod` — `e(na/q) = e((n mod q)a/q)`; the two arguments differ by the integer `(n/q)·a`.
- `sum_circleFreq_eq_residue` — **`∑_{n ∈ A} e(na/q) = ∑_{h<q} #{n ∈ A : n ≡ h} · e(ha/q)`**, with
  `residueCount` naming the class counts.

All unconditional. The exponential sum of an arbitrary finite set now collapses to a sum of length
`q` in the residue counts, which is the form Montgomery's sieve inequality needs before Parseval
over the residues turns it into a count.

### Formal layer — Parseval over the residues

`formal/GaloisForLFunctions/RHTower/Sieve/ResidueParseval.lean` turns the exponential sum of a set
into a count.

- `countVec`, `norm_inner_expRow_countVec` — the residue counts as a Euclidean vector; its
  coefficient against an exponential row *is* the exponential sum (up to conjugation, the counts
  being real).
- `norm_sq_countVec` — its energy is `∑_h A_h²`.
- `sum_residue_parseval` — `∑_{a<q} |∑_h A_h e(ha/q)|² = q ∑_h A_h²`.
- `sum_full_expSum_sq` — **`∑_{a<q} |∑_{n ∈ A} e(na/q)|² = q ∑_{h<q} #{n ∈ A : n ≡ h}²`**.

All unconditional. No new orthogonality was needed: the corpus's orthonormal root basis
(`DiscreteParseval.sum_norm_inner_expRow_root`) applies directly once the count vector is identified
as the vector whose exponential-row coefficients are the values of the sum.

This is the identity by which a sieve hypothesis becomes a count — bounding the left side below by
the classes `A` avoids and above by the large sieve bounds `|A|`, which is Montgomery's sieve
inequality. The remaining step is the passage from all residues `a < q` to the primitive ones
`(a,q) = 1`, where the large sieve lives.

### Formal layer — omitted classes force large exponential sums

`formal/GaloisForLFunctions/RHTower/Sieve/MontgomerySieve.lean` builds the lower-bound half of
Montgomery's sieve, the counterpart to the large sieve's upper bound.

- `occupiedClasses`, `sum_residueCount`, `sum_residueCount_occupied` — the classes `A` meets, and
  the fact that the counts sum to `|A|`.
- `sq_card_le_occupied_mul` — Cauchy–Schwarz over the occupied classes: `|A|² ≤ c ∑_h A_h²`.
- `expSum_zero` — `S(0) = |A|`.
- `occupied_mul_sum_nonzero_ge` — **`|A|²(q − c) ≤ c ∑_{a ≠ 0} |S(a/q)|²`**, `c` the number of
  occupied classes.

All unconditional. A set missing many residue classes modulo `q` therefore has large exponential
sums at the fractions with denominator `q`; the large sieve bounds those same sums from above, and
the two together bound `|A|`.

The inequality is deliberately stated multiplicatively rather than as `∑_h A_h² ≥ |A|²/c`, so it
stays true (and vacuous) when `A` is empty and `c = 0` — the divided form would be junk there.

### Formal layer — the large sieve for a set of integers

`formal/GaloisForLFunctions/RHTower/Sieve/IndicatorExpSum.lean` applies the sieve at an indicator,
which is where a set of integers enters.

- `circleFreq_pow` — `e(θ)^n = e(nθ)`.
- `indicatorVec`, `expSum_indicatorVec` — the trigonometric polynomial of an indicator is the
  exponential sum of the set.
- `sum_normSq_indicatorVec` — its energy is `|A|`.
- `largeSieve_set_fareySet` — **`∑_{(a,q) Farey of order Q} |∑_{n ∈ A} e(na/q)|² ≤
  (N + Q²(1 + log(Q²/2+1))) |A|`** for `A ⊆ [0,N)`.

All unconditional. This is the upper-bound half in the form Montgomery's sieve needs; the
lower-bound half (`occupied_mul_sum_nonzero_ge`) is already present. The two now speak about the
same object — the exponential sum of a set of integers at fractions — so the only remaining step to
a sieve bound on `|A|` is the observation that for prime `q` the non-zero residues are exactly the
primitive ones, and the sum over primes `q ≤ Q` of the Farey contributions.

### Formal layer — the prime fibre

`formal/GaloisForLFunctions/RHTower/Sieve/PrimeFibre.lean` identifies the index sets of the two
halves of Montgomery's sieve at a prime denominator.

- `sum_erase_fin_eq_range` — erasing the zero frequency over `Fin p` or over `range p` gives the
  same sum.
- `fareySet_fibre_prime` — the fibre of the Farey set of order `Q` above a prime `p ≤ Q` is exactly
  `{a/p : 1 ≤ a < p}`; a numerator coprime to a prime is a numerator not divisible by it.
- `sum_fareySet_fibre_eq` — **the lower bound's index set (nonzero residues mod `p`) is the prime
  fibre of the Farey set**, so `∑_{a ≠ 0} |S(a/p)|²` is literally a sub-sum of what the large sieve
  bounds.

All unconditional. With this, `occupied_mul_sum_nonzero_ge` and `largeSieve_set_fareySet` are
statements about the same sums, and the sieve inequality follows by summing the fibres over primes
`p ≤ Q` (they are disjoint subsets of the Farey set) and dividing by `|A|`.

### Formal layer — Montgomery's sieve inequality (complete)

`formal/GaloisForLFunctions/RHTower/Sieve/MontgomeryInequality.lean` closes the chain:

- `occupiedClasses_card_pos` — a nonempty set meets at least one class.
- `montgomery_sieve` — **`|A| ∑_{p ∈ P} (p − c_p)/c_p ≤ N + Q²(1 + log(Q²/2 + 1))`** for
  `A ⊆ [0,N)` nonempty, `P` any family of primes `≤ Q`, and `c_p` the number of residue classes
  modulo `p` that `A` meets.

Unconditional. A set omitting many residue classes modulo many primes is small — the sieve
statement itself, not an ingredient of one.

The full chain, all unconditional, all in `RHTower/Sieve/`: Bessel with an assumed `Δ`
(`LargeSieveWeak`) → separation (`SeparatedPoints`, `SeparatedRowSum`) → circle distance and chord
bound (`CircleSeparation`, `CircleDistance`) → circle row sum (`CircleRowSum`) → closed form
(`HarmonicLogBound`, `LargeSieveExplicit`) → Farey separation and coprimality (`FareySeparation`,
`FareyCoprime`, `FareySet`) → exponential sums (`LargeSieveExpSum`, `IndicatorExpSum`) → residues
and Parseval (`ResidueSum`, `ResidueParseval`) → the lower bound (`MontgomerySieve`) → the prime
fibre (`PrimeFibre`) → this inequality. The dual form (`LargeSieveDual`) runs alongside for
Halász–Montgomery.

The one quantitative gap to the classical statement remains the logarithmic factor, and
`sum_inv_abs_dist_le` proves it is the ceiling of the absolute-value method rather than an artefact
of this assembly.

### Formal layer — the sieve bound in usable form

`formal/GaloisForLFunctions/RHTower/Sieve/SieveBound.lean` restates the sieve the way applications
quote it: in terms of the classes *omitted* rather than those occupied.

- `deficiency_ge` — `(p − c_p)/c_p ≥ w_p/(p − w_p)` when `A` misses at least `w_p` classes; the
  deficiency ratio decreases as occupancy grows.
- `card_mul_omitted_le` — **`|A| ∑_{p ∈ P} w_p/(p − w_p) ≤ N + Q²(1 + log(Q²/2+1))`**.
- `card_le_of_sieve` — **`|A| ≤ (N + Q²(1 + log(Q²/2+1))) / L`** for any positive `L` bounding the
  sum from below.

All unconditional. The hypothesis is now the natural one — "`A` omits at least `w_p` classes mod
`p`" — with no reference to the internal occupancy count, so the sieve can be applied without
unfolding its proof.

### Formal layer — the sieve is non-vacuous

`formal/GaloisForLFunctions/RHTower/Sieve/SquareSieve.lean` exhibits the chain producing a real
bound, not merely an inequality between defined quantities.

- `third_le_ratio` — omitting half the classes gives `w/(p − w) ≥ 1/3` (the value at `w = (p−1)/2`,
  `p = 2`; it improves to `1` as `p` grows).
- `card_le_of_half_omitted` — **`|A| ≤ 3(N + Q²(1 + log(Q²/2+1)))/|P|`** for a set missing at least
  half the residue classes modulo each prime of a family `P` of primes `≤ Q`.

Both unconditional. No prime counting enters — only `|P|` — so the statement is self-contained, and
it is the classical square-root phenomenon: with `Q` of order `√N` the bound is `≍ N log N / |P|`.

This settles that the sieve layer is inhabited rather than formally true and empty, which is the
standard failure mode for a formalised inequality chain.

### Formal layer — Dirichlet rows (toward Matomäki–Radziwiłł)

The card's sole remaining input is Matomäki–Radziwiłł's Theorem 2. Its proof runs through mean
values of Dirichlet polynomials, and `formal/GaloisForLFunctions/RHTower/Sieve/DirichletRow.lean`
sets up that frame in the corpus.

- `dirRow N t` — the row `n ↦ n^{it} = exp(it log n)`, `1 ≤ n ≤ N`.
- `norm_dirRow_coord`, `norm_dirRow_sq` — the rows are unimodular coordinatewise, so `‖dirRow‖² = N`.
- `inner_dirRow` — the Gram entry is the exponential sum `∑_{n ≤ N} n^{i(u−t)}`.
- `dirichlet_bessel`, `dirichlet_bilinear` — **Halász–Montgomery for Dirichlet polynomials**: the
  mean square over a family of frequencies is controlled by the largest Gram row, in both the Bessel
  and bilinear pairings.

All unconditional; the almost-orthogonality bound they rest on
(`AlmostOrthogonality.sum_norm_inner_sq_le_of_schur`) was already corpus-owned.

What is *not* proved here, and is the next analytic obligation, is the estimate for
`∑_{n ≤ N} n^{iu}` at `u ≠ 0` — the input that makes the Gram rows small. The corpus's Abel
summation layer is the natural tool. This module is the frame that estimate drops into; it does not
assume it.

### Formal layer — the trivial Dirichlet benchmark

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletTrivial.lean` records what the analytic input
must beat.

- `inner_dirRow_self` — the diagonal Gram entry is exactly `N`.
- `norm_inner_dirRow_le` — every Gram entry is at most `N` in modulus.
- `dirichlet_pointwise` — `|F(t)|² ≤ N ∑_n |a_n|²`.
- `dirichlet_bessel_trivial` — `∑_r |F(t_r)|² ≤ R N ∑_n |a_n|²`.

All unconditional and deliberately crude. Their role is to make the content of a genuine mean value
theorem explicit: it is that the *off-diagonal* Gram entries `∑_{n ≤ N} n^{i(u−t)}` are much smaller
than `N` for separated frequencies, so the Gram row is dominated by its diagonal term. Nothing in
the corpus assumes that yet; the next analytic obligation is exactly that estimate.

### Formal layer — the near-diagonal half

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLipschitz.lean`:

- `norm_exp_phase_sub_le` — the phase exponential is 1-Lipschitz, `‖e^{ia} − e^{ib}‖ ≤ |a − b|`
  (the chord never exceeds the arc; proved from the corpus's `norm_exp_I_sub_one`).
- `norm_inner_dirRow_sub_card_le` — **`‖⟪dirRow N t, dirRow N u⟫ − N‖ ≤ |u − t| ∑_{n ≤ N} log n`**.

Both unconditional. This is the *near-diagonal* half of the mean value problem, and it is a genuine
constraint rather than a step: no cancellation whatever is available while the frequencies stay
within `≈ 1/log N` of each other, so any separation hypothesis that a mean value theorem uses must
exceed that scale. It is proved independently of the far-field estimate and does not assume it.

The complementary far-field estimate — cancellation in `∑_{n ≤ N} n^{iv}` for `|v|` large — remains
the open analytic obligation. The corpus's `HTGeometry/DirichletLinePartialSum.lean` carries out
exactly this Euler–Maclaurin comparison for the *one-line* exponent `x^{-1+iα}`; the zero-line case
`x^{iv}` needs the same argument with antiderivative `x^{1+iv}/(1+iv)`, whose telescoped part is of
size `N/|1+iv|` rather than `1/|α|`.

### Formal layer — the zero-line power

`formal/GaloisForLFunctions/RHTower/Sieve/ZeroLinePower.lean` builds the analytic objects the
far-field estimate needs, mirroring `HTGeometry/DirichletLinePartialSum.lean` at the abscissa
`Re s = 0`.

- `zpow0 v x = x^{iv}`, `Zpow0 v x = x^{1+iv}/(1+iv)`.
- `one_add_mul_I_ne_zero` — the denominator never vanishes (its real part is `1`), so no hypothesis
  `v ≠ 0` is needed anywhere in this layer.
- `norm_zpow0` — the power is unimodular.
- `exp_one_add_mul_log`, `norm_Zpow0` — `‖Zpow0 v x‖ = x/‖1+iv‖`.
- `hasDerivAt_zpow0`, `hasDerivAt_Zpow0` — **the antiderivative differentiates to the power**.
- `continuousOn_zpow0`, `intervalIntegrable_zpow0` — the hypotheses an interval integral consumes.

All unconditional. The contrast with the one-line case is the size of the antiderivative: constant
`1/|α|` there, growing like `x` here. That is exactly why `∑_{n ≤ N} n^{iv}` is of size `N/‖1+iv‖`
rather than `O(1)`, and it is the source of the `N` in the mean value theorem.

Remaining for the far-field estimate: the fundamental theorem of calculus on `[k, k+1]`, the
correction bound `‖x^{iv} − k^{iv}‖ ≤ |v|/k` (which follows from `norm_exp_phase_sub_le` already
proved), telescoping, and the harmonic sum — for which `sum_Icc_one_div_le_one_add_log` is in place.

### Formal layer — the far-field estimate

`formal/GaloisForLFunctions/RHTower/Sieve/ZeroLineSum.lean` proves the estimate the mean value
theorem was waiting on.

- `integral_zpow0_eq` — FTC for the zero-line power.
- `norm_zpow0_sub_le` — `‖x^{iv} − k^{iv}‖ ≤ |v|/k` on `[k, k+1]`, from the 1-Lipschitz phase bound
  and `log(x/k) ≤ 1/k`.
- `norm_zpow0_sub_integral_le` — the Euler–Maclaurin correction at one step.
- `norm_sum_zpow0_le` — **`‖∑_{n ≤ N} n^{iv}‖ ≤ (N+2)/‖1+iv‖ + |v|(1 + log N)`**.

All unconditional. For a frequency difference with `1 ≪ |v| ≪ N/log N` this is far below the trivial
bound `N` of `DirichletTrivial.lean`, so the Gram row of a separated family of frequencies is
dominated by its diagonal term — which is precisely the content a mean value theorem needs and which
nothing in the corpus previously supplied.

The two competing terms `N/‖1+iv‖` and `|v| log N` are why a mean value theorem carries both an `N`
and a term growing with the number of frequencies; they cross at `|v| ≍ √(N/log N)`.

### Formal layer — the Gram entry bracketed on both sides

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletFarField.lean` connects the analytic estimate to
the Halász–Montgomery frame.

- `inner_dirRow_eq_sum_zpow0` — **the Gram entry is the zero-line exponential sum**,
  `⟪dirRow N t, dirRow N u⟫ = ∑_{n ≤ N} n^{i(u−t)}`.
- `norm_inner_dirRow_le_far`, `abs_le_norm_one_add_mul_I`, `norm_inner_dirRow_le_gap` —
  **`‖⟪dirRow N t, dirRow N u⟫‖ ≤ (N+2)/|u−t| + |u−t|(1 + log N)`**.

All unconditional. With `DirichletLipschitz.norm_inner_dirRow_sub_card_le` the Gram entry is now
bracketed from both sides: within `|u−t| ≪ 1/log N` of the diagonal it is close to `N`, and once
`|u−t|` exceeds `1` while staying below `N/log N` it is much smaller than `N`. That transition is
the whole content a mean value theorem exploits, and both halves are now proved in the corpus.

### Formal layer — a mean value theorem for Dirichlet polynomials

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletMeanValue.lean`:

- `ne_of_gap` — separated frequencies are pairwise distinct.
- `dirichlet_meanValue` — for `F(t) = ∑_{n ≤ N} a_n n^{it}` and frequencies `τ` with consecutive
  gaps at least `δ`, all within a window of length `V`:

  **`∑_{r < R} |F(τ_r)|² ≤ (N + 2(N+2)(1 + log R)/δ + R V (1 + log N)) ∑_n |a_n|²`.**

Unconditional. The diagonal contributes `N`, the reciprocal separations a harmonic sum (bounded by
`SeparatedRowSum.lean`), and the linear term of the far-field estimate the spread. This beats the
trivial `R N` of `DirichletTrivial.lean` whenever `R` is large compared with `log R`, so it is a
genuine mean value theorem rather than a restatement.

It is *not* the sharp Montgomery–Vaughan form. The factor `log R` multiplying `N` is the price of
bounding `∑_{t ≠ r} |τ_t − τ_r|^{-1}` term by term, and `sum_inv_abs_dist_le` proves that price is
unavoidable for any absolute-values argument. That is the same obstruction that caps the large sieve
constant in this folder: the two open quantitative problems in the corpus's analytic layer are one
problem, namely obtaining cancellation in a sum of reciprocal separations rather than bounding it.

### Formal layer — Gallagher's Sobolev lemma

`formal/GaloisForLFunctions/RHTower/Sieve/GallagherSobolev.lean`:

- `gallagher_sobolev` — **`|f(a)| ≤ (2h)^{-1} ∫_{a−h}^{a+h} |f| + ∫_{a−h}^{a+h} |f'|`** for `f` with a
  derivative on the interval and `f'` continuous there.

Unconditional. FTC plus averaging: `f(a) = f(x) + ∫_x^a f'` for every `x` in the interval, so
`|f(a)| ≤ |f(x)| + ∫|f'|`, and integrating in `x` over a window of length `2h` gives the bound.

This opens the route past the obstruction that caps every other constant in this folder. The bound
`sum_inv_abs_dist_le` proves unavoidable applies to arguments that form a sum of reciprocal
separations; Gallagher's proof of the large sieve never forms one. Applied to `|S|²` at separated
points the surrounding intervals are *disjoint*, so the local averages assemble into `∫_0^1 |S|²` and
`∫_0^1 |S||S'|`, which Parseval evaluates — yielding a constant of the sharp shape `N + δ^{-1}` with
no logarithm, for both the large sieve and the Dirichlet mean value theorem.

Remaining for that route: Parseval on the circle for trigonometric polynomials and the derivative
identity `∫ |S'|² = ∑ (2πn)² |a_n|²`, then the disjointness assembly.

### Formal layer — orthogonality of the characters

`formal/GaloisForLFunctions/RHTower/Sieve/CircleOrthogonality.lean`:

- `circleFreq_intCast` — the characters take the value `1` at the integers.
- `circleAnti`, `hasDerivAt_circleAnti` — the explicit antiderivative `e(kt)/(2πik)` of a nonzero
  character.
- `intervalIntegrable_circleFreq_mul` — continuity, hence interval-integrability.
- `integral_circleFreq_intCast` — **`∫_0^1 e(kt) dt = 1` if `k = 0`, else `0`.**

All unconditional, and proved entirely on `[0,1]` with Lebesgue measure via the fundamental theorem
of calculus. This deliberately avoids the additive circle: mathlib's torus Fourier development uses
a file-local `MeasureSpace` instance on `AddCircle` that is not defeq to the global one, so
importing its orthogonality would force the corpus to re-declare that instance. The antiderivative
argument needs none of it — the periodicity that makes the endpoints cancel is just
`e(k) = 1` for integral `k`.

This is the orthogonality that converts `∫_0^1 |S|²` into `∑_n |a_n|²`, the remaining analytic input
for Gallagher's route to the sharp constant.

### Formal layer — the squared modulus of a trigonometric polynomial

`formal/GaloisForLFunctions/RHTower/Sieve/TrigExpansion.lean`:

- `expSum_eq_sum` — the trigonometric polynomial as a sum of characters, `S(t) = ∑_n c_n e(nt)`.
- `normSq_expSum_eq` — **`|S(t)|² = ∑_m ∑_n c_m conj(c_n) e((m−n)t)`**.
- `integral_cross_term` — **`∫_0^1 e((m−n)t) dt = 1` if `m = n`, else `0`**.

All unconditional. These are the two ingredients of Parseval for trigonometric polynomials; the only
step left is interchanging the integral with the two finite sums, after which
`∫_0^1 |S|² = ∑_n |c_n|²` and Gallagher's route to the sharp large sieve constant has all its
analytic inputs.

### Formal layer — Parseval for trigonometric polynomials

`formal/GaloisForLFunctions/RHTower/Sieve/TrigParseval.lean`:

- `intervalIntegrable_circleFreq_sub` — the cross-term characters are interval-integrable.
- `integral_normSq_expSum` — **`∫_0^1 |S(t)|² dt = ∑_{n < N} |c_n|²`** for `S(t) = ∑_{n<N} c_n e(nt)`.

Unconditional. The double sum of `TrigExpansion.lean` is interchanged with the integral (finitely
many integrable terms), orthogonality kills every off-diagonal term, and `c_n conj(c_n) = |c_n|²`
remains on the diagonal.

With `gallagher_sobolev`, `integral_circleFreq_intCast` and this identity, all three analytic inputs
of Gallagher's route to the sharp large sieve are now in the corpus. What remains is the assembly:
the derivative energy `∫_0^1 |S'|² = ∑_n (2πn)² |c_n|²` and the disjointness argument turning local
averages at `δ`-separated points into a single integral over `[0,1]`.

### Formal layer — the derivative energy

`formal/GaloisForLFunctions/RHTower/Sieve/TrigDerivative.lean`:

- `hasDerivAt_circleFreq_mul` — the derivative of a single character.
- `derivCoeff`, `hasDerivAt_expSum` — **the derivative of a trigonometric polynomial is again one**,
  with coefficients multiplied by `2πin`.
- `integral_normSq_derivCoeff` — **`∫_0^1 |S'|² = ∑_{n<N} (2πn)² |c_n|²`**.

All unconditional. Because the derivative is itself a trigonometric polynomial, its energy needs no
new analysis: Parseval applies to the new coefficient vector, and the norm computation
`‖2πin·c_n‖ = 2πn‖c_n‖` finishes it.

Both integrals appearing in Gallagher's Sobolev bound are now expressed in the coefficient energy.
The only remaining step to the sharp large sieve constant is the disjointness assembly: at
`δ`-separated points the surrounding intervals of length `δ` do not overlap, so summing the local
bounds gives one integral over `[0,1]` and the constant `N + δ^{-1}` in place of the logarithmic one.

### Formal layer — the derivative of the squared modulus

`formal/GaloisForLFunctions/RHTower/Sieve/TrigNormSqDeriv.lean`:

- `continuous_expSum` — a trigonometric polynomial is continuous.
- `hasDerivAt_normSq_expSum` — **`(|S|²)' = ⟪S, S'⟫ + ⟪S', S⟫`**, obtained by writing the squared
  modulus as the *real* inner product `⟪S, S⟫` on `ℂ` and differentiating the bilinear pairing.
- `abs_deriv_normSq_le` — **`|(|S|²)'| ≤ 2‖S‖‖S'‖`** by Cauchy–Schwarz.

All unconditional. Viewing `|z|²` as a real inner product rather than `re² + im²` avoids
differentiating the components separately; mathlib's `HasDerivAt.inner` then gives the product rule
in one step.

Gallagher's Sobolev bound applied to `f = |S|²` now has both of its integrals expressed in `|S|` and
`|S'|`, which Parseval and the derivative energy evaluate. The remaining step is the disjointness
assembly at `δ`-separated points.

### Formal layer — Gallagher's bound at a point

`formal/GaloisForLFunctions/RHTower/Sieve/GallagherPointwise.lean`:

- `gallagher_at_point` — **`|S(a)|² ≤ δ^{-1} ∫_{a−δ/2}^{a+δ/2} |S|² + ∫_{a−δ/2}^{a+δ/2} 2|S||S'|`**
  for any trigonometric polynomial `S` and any `δ > 0`.

Unconditional, and with no integrability side conditions: every ingredient is continuous, so the
Sobolev lemma's hypotheses are discharged from `continuous_expSum` alone.

This is the local half of Gallagher's argument, now in a form specialised to trigonometric
polynomials. The remaining step is global: the windows of length `δ` around `δ`-separated points are
pairwise disjoint, so summing this bound over such a family replaces the local integrals by a single
integral over one period, which `TrigParseval.lean` and `TrigDerivative.lean` evaluate as
`∑_n |c_n|²` and `∑_n (2πn)²|c_n|²`. That yields the constant `N + δ^{-1}` in place of the
logarithmic one — the sharp shape.

### Formal layer — disjoint windows

`formal/GaloisForLFunctions/RHTower/Sieve/WindowDisjointness.lean`:

- `sum_window_le` — **`∑_{r ≤ R} ∫_{λ_r−δ/2}^{λ_r+δ/2} g ≤ ∫_A^{λ_R+δ/2} g`** for continuous
  nonnegative `g` and points with consecutive gaps at least `δ`.

Unconditional. The separation gives `λ_r + δ/2 ≤ λ_{r+1} − δ/2`, so the windows do not overlap and
the induction step splits the enclosing integral into the part already counted, a gap carrying a
nonnegative integrand, and the new window. No measure theory beyond additivity over adjacent
intervals is used — in particular no `Set.PairwiseDisjoint` or `integral_iUnion`, which the ordered
case makes unnecessary.

This is the global half of Gallagher's argument. Applied to `g = |S|²` and `g = 2|S||S'|` it converts
the local bounds of `GallagherPointwise.lean` into integrals over a single enclosing interval, which
`TrigParseval.lean` and `TrigDerivative.lean` evaluate in the coefficient energy.

### Formal layer — Gallagher's bound over a separated family

`formal/GaloisForLFunctions/RHTower/Sieve/GallagherSum.lean`:

- `gallagher_sum` — **`∑_{r ≤ R} |S(λ_r)|² ≤ δ^{-1} ∫_A^{λ_R+δ/2} |S|² + ∫_A^{λ_R+δ/2} 2|S||S'|`**
  for points with consecutive gaps at least `δ`.

Unconditional. The right-hand side no longer mentions the points at all — only the enclosing
interval. That is the substance of the method: no sum of reciprocal separations is ever formed, so
the logarithmic loss `sum_inv_abs_dist_le` proves unavoidable for term-by-term arguments simply does
not arise here.

What remains to the sharp constant is arithmetic on the right-hand side: Cauchy–Schwarz on
`∫ |S||S'|`, then `TrigParseval.lean` and `TrigDerivative.lean` to replace the two integrals by
`∑_n |c_n|²` and `∑_n (2πn)² |c_n|²`, giving `δ^{-1} + 4πN` in place of the current
`N + O(δ^{-1} log δ^{-1})`.

### Formal layer — splitting the mixed term

`formal/GaloisForLFunctions/RHTower/Sieve/AmGmIntegral.lean`:

- `two_mul_le_amgm` — `2ab ≤ ε a² + ε^{-1} b²` for every `ε > 0`, from `(εa − b)² ≥ 0`.
- `integral_mixed_le` — **`∫ 2|S||S'| ≤ ε ∫ |S|² + ε^{-1} ∫ |S'|²`**.

Both unconditional. The pointwise inequality is used rather than Cauchy–Schwarz for integrals: it
keeps the argument elementary, avoids any `L^p` theory, and leaves `ε` free so the two contributions
can be balanced at the end. Choosing `ε = 2πN` will make both equal, since the derivative energy
carries the factor `(2πN)²`.

With `gallagher_sum` this reduces the sharp large sieve to the two energies alone. What remains is
substituting Parseval and the derivative energy over a full period and choosing `ε`.

### Formal layer — the large sieve with the SHARP constant

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveGallagher.lean`:

- `gallagher_period` — Gallagher's bound with both integrals over a full period.
- `largeSieve_gallagher` — **`∑_{r ≤ R} |S(λ_r)|² ≤ (δ^{-1} + 4πN) ∑_{n < N} |c_n|²`** for
  `S(t) = ∑_{n<N} c_n e(nt)` and points inside one period with consecutive gaps at least `δ`.

Unconditional. **The constant has the sharp shape `N + δ^{-1}` — the logarithm is gone.**

This settles the quantitative question left open by the earlier chain in this folder. The weak form
(`largeSieve_separated_explicit`) carries `Δ = N + O(δ^{-1} log δ^{-1})`, and `sum_inv_abs_dist_le`
proves that logarithm is unavoidable for *any* argument that bounds `∑_{t ≠ r} |λ_t − λ_r|^{-1}` term
by term. Gallagher's route reaches the sharp constant by never forming that sum at all: the local
Sobolev bounds at the separated points are absorbed into a single integral over the period by
disjointness of their windows, and the two resulting energies are evaluated by Parseval and the
derivative energy, with the AM–GM parameter set to `2πN` to balance them.

Both statements now coexist in the corpus, and neither contradicts the other: the no-go applies to
the method, not to the theorem.

### Formal layer — the sharp large sieve for finitely many points

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveFinite.lean`:

- `extendSeq`, `extendSeq_of_le`, `gap_extendSeq` — a finite family of points continued
  arithmetically past the last one; the continuation keeps the gap at every step and changes nothing
  below `R`.
- `largeSieve_gallagher_finite` — **`∑_{r ≤ R} |S(λ_r)|² ≤ (δ^{-1} + 4πN) ∑_{n<N} |c_n|²`**, needing
  the gap only between consecutive points that are actually used.

All unconditional. `largeSieve_gallagher` asks for a sequence whose *every* consecutive gap is at
least `δ`, which no application can supply — points come in finite families. The arithmetic
continuation removes that mismatch without touching the proof.

Note that `gap_extendSeq` needs no positivity hypothesis on `δ`: continuing by arithmetic steps
preserves the inequality whatever the sign, and the linter caught the unused assumption.

### Formal layer — the sharp large sieve for a separated set

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveFinset.lean`:

- `largeSieve_gallagher_finset` — **`∑_{x ∈ s} |S(x)|² ≤ (δ^{-1} + 4πN) ∑_{n<N} |c_n|²`** for any
  finite `s ⊆ [δ/2, 1−δ/2]` whose distinct elements are `δ` apart.

Unconditional. Applications supply a *set* with pairwise separation, never an increasing sequence;
listing the set in increasing order (`Finset.orderIsoOfFin`) converts pairwise separation into
consecutive separation, because for an increasing enumeration the consecutive gap is the smallest
one. The reindexing of the sum is the order isomorphism.

The sharp constant is now available in the form a sieve argument consumes — the same interface as
the weak `largeSieve_separated_explicit`, but with `δ^{-1} + 4πN` in place of
`N + O(δ^{-1} log δ^{-1})`. For the Farey set of order `Q` (`δ = Q^{-2}`, established by
`fareySet_sep`) this reads `Q² + 4πN`, the classical `N + Q²` up to the constant.

### Formal layer — the sharp bound from circle separation

`formal/GaloisForLFunctions/RHTower/Sieve/LargeSieveCircleSharp.lean`:

- `toIntDist_le_abs` — the circle distance never exceeds the ordinary one (it is the distance to the
  *nearest* integer, and `0` is one of them).
- `largeSieve_gallagher_circle` — **the sharp bound `(δ^{-1} + 4πN)` under a `ℝ/ℤ`-separation
  hypothesis**, which is the form arithmetic families supply.

Unconditional. This is the last interface mismatch: `fareySet_sep` and every other arithmetic
separation statement in this folder bound `toIntDist`, whereas Gallagher's argument is stated for
real separation. Circle separation is the stronger hypothesis, so the implication is one lemma.

Caveat recorded for the Farey instantiation: `fareySet Q` as defined here contains the pair `(1,1)`,
whose value is the endpoint `1`, and the window condition `x + δ/2 ≤ 1` excludes it. The set the
sharp bound applies to is the *proper* Farey set `1 ≤ a < q ≤ Q`, which lies in
`[Q^{-1}, 1 − Q^{-1}] ⊆ [δ/2, 1 − δ/2]` for `δ = Q^{-2}`. That restriction is genuine, not an
artefact — the endpoint and `0` are the same point of `ℝ/ℤ`, so they cannot both sit in an interval
of the line.

### Formal layer — the SHARP arithmetic large sieve

`formal/GaloisForLFunctions/RHTower/Sieve/FareySharp.lean`:

- `properFareySet`, `properFareyReals`, `mem_properFareySet` — the proper Farey fractions of order
  `Q` (reduced `a/q` with `1 ≤ a < q ≤ Q`) and their values.
- `largeSieve_farey_sharp` — **`∑_{a/q} |S(a/q)|² ≤ (Q² + 4πN) ∑_{n<N} |c_n|²`** for `Q ≥ 2`.

Unconditional. This is the classical `N + Q²` up to the absolute constant, with **no logarithm** —
the arithmetic form of the sharp large sieve, and the endpoint of the Gallagher construction begun
sixteen modules ago.

Compare `largeSieve_expSum_farey` earlier in this folder, which gives
`N + Q²(1 + log(Q²/2 + 1))` over the full Farey set. Both are proved; the sharp one restricts to the
proper fractions, for the reason recorded above: `1/1` has value `1`, the same point of `ℝ/ℤ` as `0`,
and no interval of the line can contain both while keeping the family separated.

The route's large-sieve input is therefore complete at the classical strength, in both the
inner-product, exponential-sum, and arithmetic formulations.

### Formal layer — the sharp sieve indexed by fractions

`formal/GaloisForLFunctions/RHTower/Sieve/FareySharpSet.lean`:

- `properFarey_val_injOn` — distinct proper Farey fractions have distinct values (immediate from the
  separation, since a zero circle distance would contradict it).
- `sum_properFareyReals_eq` — the sum over values equals the sum over fractions.
- `largeSieve_set_properFarey` — **`∑_{1 ≤ a < q ≤ Q, (a,q)=1} |∑_{n ∈ A} e(na/q)|² ≤
  (Q² + 4πN)|A|`** for `A ⊆ [0,N)`.

Unconditional. `largeSieve_farey_sharp` is indexed by the *values* of the fractions, but a sieve
application presents them as pairs `(a,q)`; the two indexings agree because the values are distinct.
Specialising to an indicator gives the sharp bound in exactly the shape `MontgomerySieve.lean`
consumes.

For a prime denominator `p`, the proper fractions are `a/p` with `1 ≤ a < p` — precisely the nonzero
residues, which is what `fareySet_fibre_prime` already produces. So Montgomery's sieve inequality can
be re-derived with the constant `N + Q²` in place of `N + Q²(1 + log(Q²/2+1))` with no change to its
combinatorial half.

### Formal layer — Montgomery's sieve with the sharp constant

`formal/GaloisForLFunctions/RHTower/Sieve/MontgomerySharp.lean`:

- `properFareySet_fibre_prime` — at a prime denominator the Farey fibre is *already* proper, since a
  numerator coprime to a prime and at most it is strictly less than it.
- `montgomery_sieve_sharp` — **`|A| ∑_{p ∈ P} (p − c_p)/c_p ≤ Q² + 4πN`**.

Unconditional. This is the classical `N + Q²` in place of the earlier `N + Q²(1 + log(Q²/2+1))`. The
combinatorial half of the argument is unchanged: restricting to proper fractions costs nothing at
prime moduli, which is exactly what `properFareySet_fibre_prime` establishes, so only the analytic
input was swapped.

Both versions remain in the corpus. `montgomery_sieve` applies to any family of primes with the
weaker constant and no lower bound on `Q`; `montgomery_sieve_sharp` needs `Q ≥ 2` and `N ≥ 1` and
gives the classical constant.

### Formal layer — the sieve bound at the classical constant

`formal/GaloisForLFunctions/RHTower/Sieve/SieveBoundSharp.lean`:

- `card_mul_omitted_le_sharp` — **`|A| ∑_{p ∈ P} w_p/(p − w_p) ≤ Q² + 4πN`**.
- `card_le_of_sieve_sharp` — **`|A| ≤ (Q² + 4πN)/L`**.
- `card_le_of_half_omitted_sharp` — **`|A| ≤ 3(Q² + 4πN)/|P|`** for a set missing at least half the
  classes modulo each prime of `P`.

All unconditional. Only the analytic input differs from the logarithmic versions; `deficiency_ge`
and the `1/3` of `third_le_ratio` are reused unchanged, so the two families of statements share their
combinatorial content and differ exactly in the large sieve they invoke.

The sieve layer is therefore complete at classical strength in every formulation the route uses:
inner-product, exponential-sum, arithmetic (Farey), Montgomery's inequality, and the usable
cardinality bounds.

### Formal layer — Dirichlet polynomials and their derivatives

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletPoly.lean`:

- `dirPoly`, `dirDerivCoeff` — `F(t) = ∑_{n<N} a_n n^{it}` and the coefficients of its derivative.
- `hasDerivAt_exp_phase`, `continuous_dirPoly`, `hasDerivAt_dirPoly` — **the derivative of a
  Dirichlet polynomial is again one**, with coefficients multiplied by `i log n`.
- `hasDerivAt_normSq_dirPoly`, `abs_deriv_normSq_dirPoly_le` — `(|F|²)' = ⟪F,F'⟫ + ⟪F',F⟫` and
  `|(|F|²)'| ≤ 2‖F‖‖F'‖`.

All unconditional. These are the inputs Gallagher's Sobolev bound needs to control `F` at separated
points by integrals over an interval, which is the first step of every large-values argument for
Dirichlet polynomials.

One structural difference from the trigonometric case, recorded so it is not assumed away: there is
no Parseval for Dirichlet polynomials on a finite interval. `∫_0^T |F|²` is *not* `T ∑_n |a_n|²` — the
error term is exactly the Montgomery–Vaughan mean value theorem, whose sharp form needs the Hilbert
inequality this folder does not own. So the reduction to the integrals is what this layer supplies;
their evaluation is a separate obligation and is not smuggled in.

### Formal layer — Gallagher's reduction for Dirichlet polynomials

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletGallagher.lean`:

- `gallagher_dirPoly_at_point` — `|F(x)|² ≤ δ^{-1} ∫_{x−δ/2}^{x+δ/2} |F|² + ∫ 2|F||F'|`.
- `gallagher_dirPoly_sum` — **`∑_{r ≤ R} |F(t_r)|² ≤ δ^{-1} ∫_A^{t_R+δ/2} |F|² + ∫_A^{t_R+δ/2}
  2|F||F'|`** for points with consecutive gaps at least `δ`.

Both unconditional, and both are instantiations of the *general* `gallagher_sobolev` and
`sum_window_le` — those were stated for an arbitrary continuous function, so the Dirichlet case
needed no new analysis, only the derivative facts of `DirichletPoly.lean`.

The right-hand side depends on the points only through the enclosing interval: the discrete sum has
been traded for a continuous mean, which is the standard first step of a large-values argument.

The two integrals are *not* evaluated, and cannot be by the trigonometric route: Parseval has no
finite-interval analogue for Dirichlet polynomials. Supplying one is the Montgomery–Vaughan mean
value theorem, which remains open in this corpus alongside Matomäki–Radziwiłł.

### Formal layer — integrals of a pure phase

`formal/GaloisForLFunctions/RHTower/Sieve/PhaseIntegral.lean`:

- `integral_exp_phase_zero` — `∫_0^T e^{it·0} dt = T`.
- `integral_exp_phase` — `∫_0^T e^{itL} dt = (e^{iTL} − 1)/(iL)` for `L ≠ 0`.
- `norm_integral_exp_phase_le` — **`‖∫_0^T e^{itL} dt‖ ≤ 2/|L|`**.

All unconditional. These are the cross-term integrals of `∫_0^T |F|²` for a Dirichlet polynomial:
the diagonal terms have `L = 0` and contribute `T ∑_n |a_n|²`, while the off-diagonal terms carry
`L = log m − log n` and are bounded by `2/|log(m/n)|`.

This is the dichotomy that extracts the diagonal from the mean square — the identity underlying the
Montgomery–Vaughan mean value theorem. What that theorem adds beyond this is the bound on the
resulting off-diagonal sum `∑_{m≠n} |a_m||a_n| / |log(m/n)|`, which is a Hilbert inequality for the
frequencies `log n` and remains the open input.

### Formal layer — the squared modulus of a Dirichlet polynomial

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletExpansion.lean`:

- `exp_phase_mul_conj` — a phase times the conjugate of a phase is the phase of the difference.
- `log_succ_injective` — distinct indices give distinct frequencies, so the off-diagonal bound
  `2/|log(m/n)|` never divides by zero.
- `normSq_dirPoly_eq` — **`|F(t)|² = ∑_m ∑_n a_m conj(a_n) e^{it(log m − log n)}`**.

All unconditional. Each cross term is a pure phase, so integrating over `[0,T]` and applying the
dichotomy of `PhaseIntegral.lean` separates the diagonal (frequency zero, integral `T`) from the
off-diagonal (integral at most `2/|log(m/n)|`).

`log_succ_injective` is recorded separately because it is the fact that makes the off-diagonal bound
meaningful at all: without it the frequencies could coincide for distinct indices and the `2/|L|`
estimate would be vacuous.

### Formal layer — the mean square of a Dirichlet polynomial

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletMeanSquare.lean`:

- `integral_normSq_dirPoly_eq` — **`∫_0^T |F|² = ∑_m ∑_n a_m conj(a_n) ∫_0^T e^{it(log m − log n)}`**,
  the termwise integration of the expansion.
- `integral_dirPhase_diag` — the diagonal phase integral is `T`.
- `norm_integral_dirPhase_off` — the off-diagonal ones are at most `2/|log(m/n)|`.

All unconditional. The diagonal therefore contributes `T ∑_n |a_n|²` and the remainder is an
off-diagonal sum of reciprocal logarithmic separations, weighted by `|a_m||a_n|`.

That remainder is exactly where Montgomery–Vaughan enters, and it is *not* bounded here. Controlling
`∑_{m≠n} |a_m||a_n| / |log(m/n)|` by `∑_n |a_n|²·O(n)` is a Hilbert inequality for the frequencies
`log n` — the same obstruction `sum_inv_abs_dist_le` proves fatal to term-by-term arguments. On the
circle that obstruction was bypassed by Gallagher's method using periodicity; the frequencies `log n`
are not periodic, so the bypass does not transfer, and this is the honest boundary of the corpus's
Dirichlet layer.

### Formal layer — the diagonal extracted

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletDiagonal.lean`:

- `integral_normSq_dirPoly_sub_diag` — **`∫_0^T |F|² − T ∑_n |a_n|² = ∑_m ∑_{n ≠ m} a_m conj(a_n)
  ∫_0^T e^{it(log m − log n)}`**, an exact identity.
- `norm_integral_normSq_dirPoly_sub_diag_le` — **`‖∫_0^T |F|² − T ∑_n |a_n|²‖ ≤
  ∑_m ∑_{n ≠ m} |a_m||a_n| · 2/|log(m/n)|`**.

Both unconditional. The mean value theorem for Dirichlet polynomials is now reduced to a single
inequality: everything still missing is a bound for that off-diagonal sum.

Stated plainly, the corpus's position on this problem: the reduction is complete and exact, and the
remaining input is a Hilbert inequality for the frequencies `log n`. The circle case was settled by
Gallagher's method, but that method used periodicity — disjoint windows inside one period, and
Parseval to evaluate the resulting integrals — and neither ingredient exists for `log n`. So the
Dirichlet mean value theorem is not a corollary of what this folder proved for the large sieve; it
is a genuinely separate obligation, and it sits alongside Matomäki–Radziwiłł as the route's open
input.

### Formal layer — logarithmic separation

`formal/GaloisForLFunctions/RHTower/Sieve/LogSeparation.lean`:

- `log_sub_ge` — `log x − log y ≥ (x−y)/x` for `0 < y ≤ x`, from `log(y/x) ≤ y/x − 1`.
- `abs_log_succ_sub_ge` — **`|log(m+1) − log(n+1)| ≥ |m − n|/N`** for `m, n < N`.
- `two_div_abs_log_le` — **`2/|log(m/n)| ≤ 2N/|m − n|`**.

All unconditional. This corrects the assessment recorded two batches ago. The off-diagonal sum of the
Dirichlet mean square does *not* require a Hilbert inequality at the frequencies `log n` in order to
be bounded at all — only to be bounded *sharply*. Comparing the logarithmic separation with the
integer separation costs a factor `N`, and `N` is already the size of the mean value theorem's error
term, so the elementary comparison suffices for a mean value theorem with an `N log N` error.

Concretely: `∑_{m≠n} |a_m||a_n| · 2/|log(m/n)| ≤ 2N ∑_{m≠n} |a_m||a_n|/|m−n|`, and the right-hand
side is controlled by AM–GM plus the harmonic row sum. Montgomery–Vaughan remains needed for the
sharp error `O(N)`; it is not needed for `O(N log N)`.

### Formal layer — the integer row sum

`formal/GaloisForLFunctions/RHTower/Sieve/IntegerRowSum.lean`:

- `sum_inv_abs_int_dist_le` — **`∑_{n < N, n ≠ m} |n − m|^{-1} ≤ 2(1 + log N)`**.

Unconditional, and obtained by instantiating `SeparatedRowSum.sum_inv_abs_dist_le` at the arithmetic
progression `λ_i = i` with gap `1`, then applying the closed-form harmonic bound. No new argument
was needed: the general separated row sum proved early in this folder specialises directly.

This is the row sum that appears once `LogSeparation.lean` has traded the logarithmic separations of
a Dirichlet polynomial for integer ones. With AM–GM to decouple `|a_m||a_n|` it gives the mean value
theorem with error `O(N log N)`.

### Formal layer — the row sum over `Fin N`

`formal/GaloisForLFunctions/RHTower/Sieve/FinRowSum.lean`:

- `sum_erase_inv_abs_eq`, `sum_erase_inv_abs_range_eq` — erasing the diagonal changes neither sum.
- `sum_inv_abs_fin_dist_le` — **`∑_{n ≠ m} |n − m|^{-1} ≤ 2(1 + log N)` over `Fin N`**.

Unconditional. The Dirichlet sums of this folder are indexed by `Fin N` while the row sum was proved
over `range N`; the transfer is immediate once one notices that the omitted diagonal term is
`|m − m|^{-1} = 0` under Lean's `1/0 = 0` convention, so both erased sums equal their full sums and
`Fin.sum_univ_eq_sum_range` identifies those.

That convention is usually a nuisance; here it removes the need for any bijection between
`univ.erase m` and `(range N).erase m`.

### Formal layer — swapping the off-diagonal double sum

`formal/GaloisForLFunctions/RHTower/Sieve/OffDiagonalSwap.lean`:

- `sum_erase_eq_sum_ite` — an erased sum is the full sum with the diagonal term zeroed.
- `sum_erase_swap` — **`∑_m ∑_{n ≠ m} g m n = ∑_n ∑_{m ≠ n} g m n`**.

Unconditional. `Finset.sum_comm` cannot be applied to iterated sums whose inner index set depends on
the outer index; rewriting `univ.erase m` as `univ` with the diagonal zeroed removes that dependence
and makes the swap a one-line application.

This is the decoupling step for the Dirichlet mean value theorem: it identifies the two halves of
`∑_m ∑_{n ≠ m} (|a_m|² + |a_n|²) K(m,n)` for a symmetric kernel `K`, so the AM–GM bound on
`|a_m||a_n|` collapses to a single row sum.

### Formal layer — the off-diagonal sum bounded

`formal/GaloisForLFunctions/RHTower/Sieve/OffDiagonalBound.lean`:

- `offDiagonal_le` — **`∑_m ∑_{n ≠ m} |a_m||a_n| · 2/|log(m/n)| ≤ 4N(1 + log N) ∑_m |a_m|²`**.

Unconditional. Three steps, each already in the corpus: `LogSeparation` trades logarithmic
separations for integer ones at a cost of `N`; AM–GM decouples `|a_m||a_n|` into
`(|a_m|² + |a_n|²)/2`; `OffDiagonalSwap` identifies the two resulting halves, each a row sum bounded
by `2(1 + log N)` via `FinRowSum`.

Combined with `norm_integral_normSq_dirPoly_sub_diag_le` this gives the mean value theorem for
Dirichlet polynomials with error `O(N log N)`:

`‖∫_0^T |F|² − T ∑_n |a_n|²‖ ≤ 4N(1 + log N) ∑_n |a_n|²`.

The sharp Montgomery–Vaughan error `O(N)` still requires the Hilbert inequality at the frequencies
`log n`; the `log N` here is the price of the elementary comparison, exactly as the `log` in the weak
large sieve was.

### Formal layer — THE MEAN VALUE THEOREM FOR DIRICHLET POLYNOMIALS

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletMVT.lean`:

- `dirichlet_meanValue_complex`, `dirichlet_meanValue_theorem` —

  **`|∫_0^T |F(t)|² dt − T ∑_{n<N} |a_n|²| ≤ 4N(1 + log N) ∑_{n<N} |a_n|²`**

  for `F(t) = ∑_{n<N} a_n n^{it}`.

Unconditional. This is the mean value theorem for Dirichlet polynomials, with error `O(N log N)`.

Corrected assessment: an earlier entry on this card reported the theorem as blocked behind
Montgomery–Vaughan. That was wrong — Montgomery–Vaughan is needed only for the *sharp* error `O(N)`.
The elementary comparison between logarithmic and integer separations (`LogSeparation.lean`) costs a
factor `N`, which is already the order of the error term, so `O(N log N)` follows from material this
folder owns.

Route status: the Dirichlet-polynomial layer now has the reduction (`DirichletGallagher`), the
mean value theorem, and the large sieve at classical strength. The card's stated remaining input,
Matomäki–Radziwiłł Theorem 2, is unchanged.

### Formal layer — the derivative energy

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletDerivEnergy.lean`:

- `norm_dirDerivCoeff` — `‖i log n · a_n‖ = log n · ‖a_n‖`.
- `sum_normSq_dirDerivCoeff_le` — **`∑_{n<N} ‖i log n · a_n‖² ≤ (log N)² ∑_{n<N} ‖a_n‖²`**.

Unconditional. The largest frequency of a Dirichlet polynomial of length `N` is `log N`, so
differentiation multiplies the energy by at most `(log N)²`.

Applying the mean value theorem to `F'` — itself a Dirichlet polynomial with these coefficients —
bounds `∫_0^T |F'|²`, the second integral in Gallagher's reduction. With that and `∫_0^T |F|²`, the
reduction of `DirichletGallagher.lean` becomes a large-values estimate: a bound on
`∑_r |F(t_r)|²` at separated points purely in terms of `T`, `N` and the coefficient energy.

### Formal layer — both integrals of Gallagher's reduction

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletIntegralBound.lean`:

- `integral_normSq_dirPoly_le` — **`∫_0^T |F|² ≤ (T + 4N(1 + log N)) ∑_n |a_n|²`**.
- `window_factor_nonneg` — the factor `T + 4N(1 + log N)` is nonnegative for `T ≥ 0`.
- `integral_normSq_dirPoly_deriv_le` — **`∫_0^T |F'|² ≤ (T + 4N(1 + log N))(log N)² ∑_n |a_n|²`**.

All unconditional. The second follows from the first applied to `F'`, which is itself a Dirichlet
polynomial whose coefficient energy is at most `(log N)²` times that of `F`.

Both integrals appearing in `gallagher_dirPoly_sum` are now controlled by `T`, `N` and the
coefficient energy alone, so that reduction is no longer conditional on evaluating them. Feeding
these bounds in — with the AM–GM split of `AmGmIntegral.lean` for the mixed term — yields a
large-values estimate for Dirichlet polynomials at separated points.

### Formal layer — splitting the mixed term for Dirichlet polynomials

`formal/GaloisForLFunctions/RHTower/Sieve/AmGmDirichlet.lean`:

- `integral_mixed_dirPoly_le` — **`∫_A^B 2|F||F'| ≤ ε ∫_A^B |F|² + ε^{-1} ∫_A^B |F'|²`** for every
  `ε > 0`.

Unconditional. The pointwise inequality `two_mul_le_amgm` is shared with the trigonometric case; only
the continuity and integrability facts differ, and those come from `continuous_dirPoly`.

Every ingredient of a large-values estimate for Dirichlet polynomials is now present: the Gallagher
reduction (`DirichletGallagher`), bounds for both integrals (`DirichletIntegralBound`), and this
split. Choosing `ε = log N` — the largest frequency — equalises the two contributions and gives a
bound of the shape `(T + 4N(1 + log N))(δ^{-1} + 2 log N) ∑_n |a_n|²`.

### Formal layer — A LARGE-VALUES ESTIMATE FOR DIRICHLET POLYNOMIALS

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLargeValues.lean`:

- `largeValues_dirPoly` —

  **`∑_{r ≤ R} |F(t_r)|² ≤ (T + 4N(1 + log N))(δ^{-1} + 2 log N) ∑_{n<N} |a_n|²`**

  for `F(t) = ∑_{n<N} a_n n^{it}`, `N ≥ 2`, and points in `[δ/2, T − δ/2]` with consecutive gaps at
  least `δ`.

Unconditional. Gallagher's reduction trades the discrete sum for two integrals over `[0,T]`, the
mixed one is split with balancing parameter `log N`, and both are bounded by the mean value theorem.

This is the estimate a large-values or zero-density argument consumes, and it completes the Dirichlet
layer: reduction, mean value theorem, derivative energy, and now the large-values bound itself — all
unconditional and all at `log`-lossy but usable strength.

### Formal layer — counting large values

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletLargeValuesCount.lean`:

- `card_largeValues_le` — **`(R+1)V² ≤ (T + 4N(1 + log N))(δ^{-1} + 2 log N) ∑_{n<N} |a_n|²`**
  whenever `|F| ≥ V` at `R+1` points separated by `δ` inside `[δ/2, T − δ/2]`.

Unconditional. This is the form in which a large-values estimate is used — a cap on how often a
Dirichlet polynomial can be large — rather than a bound on a sum the caller would have to unpack.

With this the corpus's analytic layer for Route E stands complete at usable strength: the large sieve
(sharp), Montgomery's sieve (sharp), the Dirichlet mean value theorem, and the large-values estimate
with its counting form. The card's stated remaining input is unchanged: Matomäki–Radziwiłł Theorem 2.

### Corpus check — Plancherel IS in mathlib (2026-08-03)

Recorded to prevent a future session from building it.

`Mathlib/Analysis/Fourier/LpSpace.lean` supplies the `L²` Fourier theory this route's remaining
input needs:

- `fourierTransformₗᵢ : Lp F 2 ≃ₗᵢ[ℂ] Lp F 2` — the Fourier transform as a linear *isometric
  equivalence* on `L²`;
- `norm_fourier_eq : ‖𝓕 f‖ = ‖f‖` — Plancherel;
- `inner_fourier_eq : ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫` — Parseval;
- `SchwartzMap.toLp_fourier_eq`, `fourier_toTemperedDistribution_eq` — compatibility with the
  Schwartz and tempered-distribution pictures.

So the Parseval bridge Matomäki–Radziwiłł uses — passing from a short-interval average to an
integral of a Dirichlet polynomial — is an **instantiation** problem, not a construction problem.
The analytic engine exists; what has to be built is the arithmetic side: exhibiting the
short-interval average as an `L²` Fourier pair, which means a logarithmic change of variable turning
the Dirichlet series into a function on `ℝ` and identifying the resulting kernel.

Note the earlier assessment on these cards that "nothing in mathlib approaches" the remaining input
is correct about Matomäki–Radziwiłł itself and about Menon's theorem, but should not be read as
covering their analytic prerequisites: Plancherel, the large sieve, the Dirichlet mean value theorem
and the large-values estimate are all now available, the last three from this corpus.

### Formal layer — pairing a Dirichlet polynomial against a kernel

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletPairing.lean`:

- `integral_dirPoly_mul` — **`∫_A^B F(t)K(t) dt = ∑_{n<N} a_n ∫_A^B n^{it} K(t) dt`** for continuous
  `K`.

Unconditional. For a *finite* Dirichlet polynomial this is linearity of the integral, so no
convergence question arises — which is why it can be stated with no hypothesis on `K` beyond
continuity, and on any interval.

This is the finite form of the Parseval bridge. The inner integral is the transform of the kernel at
the frequency `log n`, so pairing against a kernel evaluates the coefficient sum against that
transform. Choosing `K` to concentrate near a point turns the left side into a short-interval average
and the right side into a weighted coefficient sum — the shape Matomäki–Radziwiłł's argument works
in. With `norm_fourier_eq` available from mathlib, what remains on this route is the choice of kernel
and the estimation of its transform, not the construction of the transform theory.

### Formal layer — the symmetric phase integral (Dirichlet kernel)

`formal/GaloisForLFunctions/RHTower/Sieve/SymmetricPhaseIntegral.lean`:

- `exp_phase_sub_neg` — `e^{iθ} − e^{−iθ} = 2i sin θ`.
- `integral_exp_phase_symm_zero` — `∫_{−T}^{T} e^{it·0} dt = 2T`.
- `integral_exp_phase_symm` — **`∫_{−T}^{T} e^{itL} dt = 2 sin(TL)/L`** for `L ≠ 0`.

All unconditional. Paired with a Dirichlet polynomial through `integral_dirPoly_mul`, this *is* the
Dirichlet kernel: `∫_{−T}^{T} F(t) dt = ∑_n a_n · 2 sin(T log n)/log n`, and twisting by `x^{−it}`
moves the frequencies to `log(n/x)`, so the kernel concentrates on `n ≈ x` with width `e^{1/T}`. Its
modulus is at most `min(2T, 2/|L|)`, which is what makes far frequencies negligible.

That is the concrete kernel the Parseval bridge needs; with `integral_dirPoly_mul` supplying the
pairing and mathlib supplying Plancherel, the short-interval side of Matomäki–Radziwiłł is now a
matter of estimating this kernel rather than of building transform theory.

### Formal layer — the Dirichlet kernel against a Dirichlet polynomial

`formal/GaloisForLFunctions/RHTower/Sieve/DirichletKernelPairing.lean`:

- `norm_integral_exp_phase_symm_le_inv` — the kernel decays: `‖∫_{−T}^{T} e^{itL}‖ ≤ 2/|L|`.
- `norm_integral_exp_phase_symm_le_len` — and is capped by the interval: `≤ 2T`.
- `integral_dirPoly_symm` — **`∫_{−T}^{T} F(t) dt = ∑_{n<N} a_n ∫_{−T}^{T} n^{it} dt`**.

All unconditional. The two bounds are what make the pairing *selective*: near the trivial frequency
the kernel has size `2T`, and away from it the kernel decays like the reciprocal of the frequency.
After a twist by `x^{−it}` the frequencies become `log(n/x)`, so the pairing localises the
coefficient sum to `n ≈ x` — which is the mechanism by which a short-interval average is read off a
Dirichlet polynomial.

The short-interval side of the route is therefore assembled from proved parts: pairing identity,
explicit kernel, decay and cap. What is not yet built is the quantitative localisation — turning
these into an approximation of the short-interval sum with a controlled error.

### Formal layer — linear weights against a phase

`formal/GaloisForLFunctions/RHTower/Sieve/LinearPhaseIntegral.lean`:

- `linPhaseAnti`, `hasDerivAt_linPhaseAnti` — the explicit antiderivative
  `t e^{itL}/(iL) − e^{itL}/(iL)²` of `t e^{itL}`.
- `intervalIntegrable_linPhase`, `integral_linPhase` — the resulting closed-form integral on any
  interval.

All unconditional. With the constant case of `SymmetricPhaseIntegral.lean` this computes the
transform of *every piecewise-linear kernel* in closed form.

Why that matters here rather than being a convenience: the sharp kernel `2 sin(TL)/L` decays only
like `|L|^{-1}`, so its tail over the frequencies `log(n/x)` is not absolutely summable and a
localisation argument cannot simply discard it. The triangular (Fejér) weight `1 − |t|/T` decays like
`|L|^{-2}` and is nonnegative, which is what makes the discard legitimate. Building its transform
needs exactly the linear-times-phase antiderivative proved here.

### Formal layer — the triangular weight on a half interval

`formal/GaloisForLFunctions/RHTower/Sieve/FejerHalf.lean`:

- `integral_fejerHalf_split` — **`∫_0^T (1 − t/T)e^{itL} dt = ∫_0^T e^{itL} dt −
  T^{-1} ∫_0^T t e^{itL} dt`**.

Unconditional. Both pieces on the right have closed forms already in the corpus
(`PhaseIntegral.integral_exp_phase` and `LinearPhaseIntegral.integral_linPhase`), so the triangular
weight's transform is now explicit.

Reflecting and adding gives the symmetric Fejér transform `2(1 − cos TL)/(TL²)`, which is
nonnegative — because `cos ≤ 1` — and decays like `|L|^{-2}`. Those are precisely the two properties
the sharp kernel lacks and that a localisation argument needs: nonnegativity to discard tails
without sign cancellation, and square-summable decay so the discard is quantitatively small.

### Formal layer — the half-interval Fejér transform in closed form

`formal/GaloisForLFunctions/RHTower/Sieve/FejerHalf.lean`, second theorem:

- `integral_fejerHalf` — **`∫_0^T (1 − t/T)e^{itL} dt = i/L − (e^{iTL} − 1)/(TL²)`** for `L ≠ 0`,
  `T > 0`.

Unconditional. Obtained by substituting the two closed forms into `integral_fejerHalf_split`; the
whole content is complex algebra with `i² = −1`.

Adding this to its reflection gives the symmetric Fejér transform: the `i/L` terms cancel (they are
purely imaginary and odd), leaving `2(1 − cos TL)/(TL²)` — real, nonnegative, and `O(|L|^{-2})`. The
cancellation of the `i/L` term is the point: it is the part that decays only like `|L|^{-1}`, and it
is exactly what symmetrising removes.

### Formal layer — the symmetric Fejér transform

`formal/GaloisForLFunctions/RHTower/Sieve/FejerSymmetric.lean`:

- `exp_phase_add_neg` — `e^{iθ} + e^{−iθ} = 2 cos θ`.
- `integral_fejer_symm` — **the half-interval transform at `L` plus its value at `−L` equals
  `(2 − 2 cos TL)/(TL²)`**.

Unconditional. The `i/L` terms cancel — purely imaginary and odd — and they are exactly the part
decaying only like `|L|^{-1}`. What survives is real, nonnegative (`cos ≤ 1`) and `O(|L|^{-2})`.

The transform at `−L` is what the reflection `t ↦ −t` turns the left half of a symmetric triangular
weight into, so this is the Fejér transform; stating it as a sum over the two signs avoids carrying
`|t|` through the computation and needs no change-of-variables lemma.

The smoothed kernel with the properties a localisation argument requires is therefore now explicit
and proved in the corpus.

### Formal layer — the Fejér transform's two properties

`formal/GaloisForLFunctions/RHTower/Sieve/FejerBounds.lean`:

- `fejer_transform_nonneg` — **`0 ≤ (2 − 2cos TL)/(TL²)`**.
- `fejer_transform_le_inv` — **`≤ 4/(TL²)`**, the decay.
- `fejer_transform_le_len` — **`≤ T`**, the cap near the trivial frequency.

All unconditional. The first two follow from `−1 ≤ cos ≤ 1`; the third is the quadratic bound
`1 − θ²/2 ≤ cos θ` (mathlib's `Real.one_sub_sq_div_two_le_cos`) at `θ = TL`.

Together these say the transform is a *nonnegative weight of total size `T` concentrated on
`|L| ≲ T^{-1}`, with a square-summable tail* — the three facts a localisation argument cites, now
proved rather than assumed. The sharp Dirichlet kernel satisfies the analogue of the cap but neither
of the other two.

### Formal layer — pairing a Dirichlet polynomial with the Fejér weight

`formal/GaloisForLFunctions/RHTower/Sieve/FejerPairing.lean`:

- `integral_fejerHalf_dirPoly` — **`∫_0^T F(t)(1 − t/T) dt = ∑_{n<N} a_n ∫_0^T n^{it}(1 − t/T) dt`**.
- `integral_fejer_comm` — the inner integrals in the order the closed form uses.
- `integral_fejer_zero` — **the term whose frequency vanishes contributes `T/2`**.

All unconditional. The Fejér-weighted average of a Dirichlet polynomial is therefore the coefficient
sum weighted by an explicit, nonnegative, rapidly decaying kernel, with the `n = 1` term (frequency
`log 1 = 0`) contributing the main term `a_1 · T/2` and every other term controlled by
`FejerBounds.lean`.

That separation — main term from the vanishing frequency, error from the rest — is the structure a
short-interval argument needs, and it is now proved rather than asserted.

### Formal layer — bounding the half-interval Fejér transform

`formal/GaloisForLFunctions/RHTower/Sieve/FejerHalfBound.lean`:

- `norm_integral_fejerHalf_le` — **`‖∫_0^T (1 − t/T)e^{itL} dt‖ ≤ |L|^{-1} + 2/(TL²)`**.

Unconditional. Both terms of the closed form are bounded separately: `i/L` has modulus exactly
`|L|^{-1}`, and the second term at most `2/(TL²)`.

Recorded precisely because the half-interval bound is *weaker* than the symmetric one: the
`|L|^{-1}` term is odd and cancels on symmetrising, which is what leaves the pure `|L|^{-2}` decay of
`FejerBounds.lean`. On a half interval it survives, and this is the honest bound there. A localisation
argument that works on `[0,T]` rather than `[−T,T]` therefore carries the weaker tail, and the
difference is not cosmetic — `|L|^{-1}` is not summable over the frequencies `log n` while `|L|^{-2}`
is.

### Formal layer — the symmetric Fejér pairing is real and small

`formal/GaloisForLFunctions/RHTower/Sieve/FejerSymmBound.lean`:

- `integral_fejer_symm_real` — the symmetric pairing is the cast of the real number
  `(2 − 2cos TL)/(TL²)`.
- `norm_integral_fejer_symm_le_inv` — **its modulus is at most `4/(TL²)`**.
- `norm_integral_fejer_symm_le_len` — **and at most `T`**.

All unconditional. This is the pairing a localisation argument must use, for the reason recorded on
the previous entry: the half-interval bound carries a `|L|^{-1}` term that is not summable over the
frequencies `log n`, and symmetrising cancels it exactly.

With these the short-interval side of the route is complete as a *toolkit*: pairing identity
(`integral_dirPoly_mul`), explicit kernel with closed form (`FejerHalf`, `FejerSymmetric`), the two
kernel properties (`FejerBounds`), the main-term separation (`FejerPairing`), and now the bounds in
the form a sum over `n` consumes.

### Formal layer — LOCALISATION OF A DIRICHLET POLYNOMIAL

`formal/GaloisForLFunctions/RHTower/Sieve/FejerLocalisation.lean`:

- `fejerWeightAt`, `fejerWeightAt_zero`, `norm_fejerWeightAt_le` — the symmetric Fejér weight at a
  frequency: exactly `T` at the trivial frequency, at most `4/(TL²)` elsewhere.
- `log_succ_zero`, `log_succ_ne_zero` — the frequency `log n` vanishes only at `n = 1`.
- `norm_fejer_dirPoly_sub_main_le` —

  **`‖∑_{n<N} a_n W(T, log n) − a_1 T‖ ≤ ∑_{n ≥ 2} |a_n| · 4/(T (log n)²)`**.

All unconditional. The Fejér average of a Dirichlet polynomial equals its first coefficient times
`T`, with an error governed entirely by the remaining coefficients against a square-summable kernel
tail. That is the localisation a short-interval argument performs, and it is now a theorem.

The structural point: the frequency `log n` vanishes at exactly one index, so the main term is
isolated by an algebraic fact rather than an estimate, and everything else is uniformly small. This
is what the earlier kernel work was for.

### Formal layer — the Fejér pairing as an integral

`formal/GaloisForLFunctions/RHTower/Sieve/FejerIntegralPair.lean`:

- `integral_dirPoly_neg_mul` — pairing the *reflected* polynomial `F(−t)` against a kernel negates
  the frequencies.
- `integral_fejer_pair_eq` — **`∫_0^T F(t)(1 − t/T) dt + ∫_0^T F(−t)(1 − t/T) dt =
  ∑_{n<N} a_n W(T, log n)`**.

Both unconditional. Reflecting the argument is exactly the second half of the symmetric weight, so
this needs no change of variables and no absolute value — the `|t|` that a literal symmetric
triangular weight would introduce never appears.

Composed with `norm_fejer_dirPoly_sub_main_le`, the statement is now about integrals of the
polynomial itself: **the symmetrised Fejér average of a Dirichlet polynomial over `[0,T]` is `a_1 T`
up to `∑_{n ≥ 2} |a_n| · 4/(T(log n)²)`.** That is the short-interval localisation in the form an
argument uses, with both sides expressed in the original objects rather than in kernel weights.

### Formal layer — THE SHORT-INTERVAL LOCALISATION

`formal/GaloisForLFunctions/RHTower/Sieve/FejerShortInterval.lean`:

- `norm_fejer_integral_sub_main_le` —

  **`‖∫_0^T F(t)(1−t/T) dt + ∫_0^T F(−t)(1−t/T) dt − a_1 T‖ ≤ ∑_{n ≥ 2} |a_n| · 4/(T (log n)²)`**

  for `F(t) = ∑_{n<N} a_n n^{it}`.

Unconditional, and not asymptotic: an inequality valid for every `N`, every coefficient vector and
every `T > 0`. The symmetrised Fejér average of a Dirichlet polynomial over `[0,T]` is its first
coefficient times `T`, with an error that is `O(T^{-1})` for fixed coefficients.

This completes the short-interval side of the corpus's Matomäki–Radziwiłł programme as a proved
statement rather than a toolkit. Together with the sharp large sieve, Montgomery's sieve, the
Dirichlet mean value theorem and the large-values estimate — all built in this corpus — the analytic
prerequisites of that route are in place. What remains is the multiplicative structure: the
decomposition by prime factors (for which `RamareWeight.lean` supplies the exact identity) and the
Halász-type input, neither of which is a consequence of the analytic layer alone.

### Formal layer — Ramaré's weight on a coprime factorisation

`formal/GaloisForLFunctions/RHTower/Sieve/RamarePrimeFactor.lean` opens the multiplicative side.

- `primeFactorsIn_mul_prime` — **`primeFactorsIn P (pm) = insert p (primeFactorsIn P m)`** for a
  designated prime `p ∤ m`.
- `card_primeFactorsIn_mul_prime` — hence **`ω_P(pm) = ω_P(m) + 1`**.
- `map_mul_prime_of_not_dvd` — a multiplicative `f` satisfies `f(pm) = f(p)f(m)` there.

All unconditional. These are what make Ramaré's bilinear decomposition genuinely bilinear on the
coprime part: the weight `1/ω_P(pm)` becomes `1/(ω_P(m)+1)`, a function of the cofactor alone, and
the multiplicative function factors.

Stated precisely so the limit is visible: the identities hold only where `p ∤ m`. The part with
`p ∣ m` is a remainder that a sieve must bound separately — it is not governed by these identities,
and treating the decomposition as bilinear everywhere would be wrong.

The primality hypothesis on the designated set is necessary, not decorative: `primeFactorsIn` is
defined for an arbitrary `P`, and `q ∣ pm ↔ q = p ∨ q ∣ m` requires `q` prime.

### Formal layer — the bilinear Ramaré sum for a multiplicative function

`formal/GaloisForLFunctions/RHTower/Sieve/RamareBilinearSplit.lean`:

- `sum_ramare_bilinear_split` —

  **`∑_{m ∈ T} f(pm)/ω_P(pm) = f(p) ∑_{p ∤ m} f(m)/(ω_P(m)+1) + ∑_{p ∣ m} f(pm)/ω_P(pm)`**

  for a multiplicative `f` and a designated prime `p`.

Unconditional. On the first part the function factors and the weight depends on the cofactor alone,
so the sum is genuinely bilinear in `p` and `m` — which is the structure Matomäki–Radziwiłł's
argument exploits.

The second part is isolated deliberately rather than absorbed. There `p` occurs to a higher power,
`f` does **not** factor, and a sieve must bound it separately. Quoting the Ramaré decomposition as
bilinear throughout would hide exactly the term an argument has to control, so the split is stated
with the remainder explicit.

### Formal layer — bounding the Ramaré remainder

`formal/GaloisForLFunctions/RHTower/Sieve/RamareRemainder.lean`:

- `one_le_card_primeFactorsIn_mul` — the designated prime always divides its own multiple, so
  `ω_P(pm) ≥ 1`.
- `abs_ramare_remainder_le` — **`|∑_{p ∣ m} f(pm)/ω_P(pm)| ≤ #{m ∈ T : p ∣ m}`** for `|f| ≤ 1`.

Both unconditional. This bounds the term that `RamareBilinearSplit.lean` isolates, so the
decomposition is now complete: bilinear main part plus a controlled remainder.

The bound is deliberately crude — no cancellation is used, each term simply has modulus at most one.
It suffices because the count on the right is the number of multiples of `p` in the cofactor range,
which is itself small; the corpus's `Sieve/IntervalMultiples` supplies that count. Claiming anything
sharper here would require cancellation in a sum where `f` does not factor, which is precisely what
is unavailable.

### Formal layer — THE COMPLETE MULTIPLICATIVE RAMARÉ DECOMPOSITION

`formal/GaloisForLFunctions/RHTower/Sieve/RamareDecomposition.lean`:

- `abs_ramare_inner_sub_bilinear_le` —
  **`|∑_{m∈T} f(pm)/ω_P(pm) − f(p)·B_p| ≤ #{m ∈ T : p ∣ m}`**.
- `abs_sum_ramare_sub_bilinear_le` — the same summed over the designated primes, with total error
  `∑_{p∈P} #{m ∈ T_p : p ∣ m}`.

Both unconditional, for any bounded multiplicative `f`.

Ramaré's weighted factorisation of such an `f` is therefore **bilinear up to a term counted by
multiples** — the structure Matomäki–Radziwiłł's argument requires, with its error explicit rather
than absorbed.

Route status. The corpus now owns, all unconditionally: the sharp large sieve, Montgomery's sieve,
the Dirichlet mean value theorem, the large-values estimate, the short-interval localisation, and
this multiplicative decomposition. The remaining input is the Halász-type bound — a mean-value
theorem for multiplicative functions in terms of their distance from `n^{it}` — which is a separate
theorem and not a consequence of the layers above.

### Formal layer — the distance from a character

`formal/GaloisForLFunctions/RHTower/Sieve/MultiplicativeDistance.lean` opens the Halász layer.

- `mulDistSq` — **`D(f,t;P)² = ∑_{p ∈ P} (1 − Re(f(p)p^{-it}))/p`**, the quantity Halász's theorem
  is stated in.
- `one_sub_re_nonneg`, `mulDist_term_nonneg` — each summand is nonnegative when `|f(p)| ≤ 1`.
- `mulDistSq_nonneg`, `mulDistSq_mono` — the distance is a genuine nonnegative quantity, monotone in
  the set of primes.

All unconditional.

This is the *object*, not the theorem. Halász's bound — that a multiplicative function has small mean
value unless it is close to some `n^{it}` in this distance — is a separate result and is not proved
here. Defining the distance and establishing that it is well-behaved is the prerequisite; the
inequality itself remains the route's open input, alongside nothing else.

### Formal layer — the distance is a genuine distance

`formal/GaloisForLFunctions/RHTower/Sieve/DistancePointwise.lean` and `.../DistanceTriangle.lean`.

Pointwise (`DistancePointwise`):

- `normSq_sub_eq` — the polarisation identity `‖u−v‖² = ‖u‖² + ‖v‖² − 2 Re(u conj v)`.
- `half_normSq_sub_le` — on the closed unit disc, `‖u−v‖²/2 ≤ 1 − Re(u conj v)`.
- `one_sub_re_eq_half_normSq` — on the unit circle the two are **equal**.

Global (`DistanceTriangle`):

- `mulDistSqPair` — `D(f,g;P)² = ∑_{p∈P}(1 − Re(f(p) conj g(p)))/p`.
- `distVec`, `distVec_add`, `norm_distVec` — the distance is exactly the Euclidean norm of the vector
  `p ↦ (f(p) − g(p))/√(2p)` in `EuclideanSpace ℂ P`, and that vector is additive in the middle
  argument.
- `sqrt_mulDistSqPair_triangle` — **the Granville–Soundararajan triangle inequality**
  `D(f,h;P) ≤ D(f,g;P) + D(g,h;P)` for unimodular `f, g, h`.
- `charFn`, `norm_charFn`, `conj_charFn`, `mulDistSq_eq_pair` — the character `n ↦ n^{it}` is
  unimodular and `mulDistSq f t P` is the pairwise distance to it.
- `sqrt_mulDistSq_triangle_char` — distance to a character is transitive through any unimodular
  function.

All unconditional.

The equality on the unit circle is what makes this work: it turns the distance into a norm, so the
triangle inequality is `norm_add_le` rather than an inequality needing proof. On the open disc only
the inequality `half_normSq_sub_le` survives, in the direction that does *not* give the triangle
inequality — so the unimodular hypothesis in the triangle theorem is doing real work, not tidiness.
The disc case is the Granville–Soundararajan lemma proper and is not proved here.

### Formal layer — the triangle inequality on the closed unit disc

`formal/GaloisForLFunctions/RHTower/Sieve/DistanceDiscTriangle.lean` removes the unimodularity
hypothesis, giving the Granville–Soundararajan triangle inequality in the form it is actually used.

- `sqrt_one_sub_re_triangle` — **pointwise on the closed unit disc**:
  `√(1−Re(u w̄)) ≤ √(1−Re(u v̄)) + √(1−Re(v w̄))` for `‖u‖,‖v‖,‖w‖ ≤ 1`.
- `sqrt_sum_sq_add_le` — Minkowski for a finite sum of squares, via `EuclideanSpace ℝ P`.
- `one_sub_re_mul_conj_nonneg` — the summands are nonnegative on the disc.
- `sqrt_mulDistSqPair_triangle_disc` — **the full theorem**: `D(f,h;P) ≤ D(f,g;P) + D(g,h;P)`
  for `‖f(p)‖, ‖g(p)‖, ‖h(p)‖ ≤ 1`.
- `mulDistSqPair_nonneg_disc`, `sqrt_mulDistSq_triangle_char_disc` — nonnegativity and transitivity
  of closeness to a character, on the disc.

All unconditional.

The naive comparison `C ≤ A + B` is **false** on the disc: at `u = e^{iπ/3}`, `v = 1`,
`w = e^{-iπ/3}` it reads `3/2 ≤ 1/2 + 1/2`. The cross term is not slack, it is the content. What
carries the proof is the identity `2(1−Re(u v̄)) = ‖u−v‖² + (1−‖u‖²) + (1−‖v‖²)`; writing
`2A = X²+a+b`, `2B = Y²+b+c`, `2C = Z²+a+c` gives
`4AB ≥ (X²+b)(Y²+b) = (XY+b)² + b(X−Y)²`, so `2√(AB) ≥ XY+b`, and `Z ≤ X+Y` finishes.
The slack `b(X−Y)²` — the *defect* of the middle value — is exactly what pays for the cross term,
which is why the unimodular case (`b = 0`) is the tight one.

This closes the metric geometry of the Halász distance. The mean-value bound itself remains the
route's open input.

### Formal layer — the divisor swap and Halász's recursion

`formal/GaloisForLFunctions/RHTower/Sieve/DivisorSwap.lean`.

- `sum_divisors_swap` — **the general divisor swap**
  `∑_{m ≤ N} ∑_{d ∣ m} G(d, m/d) = ∑_{d ≤ N} ∑_{k ≤ N/d} G(d,k)`, by the explicit bijection
  `(m,d) ↦ (d, m/d)` with inverse `(d,k) ↦ (dk, d)`.
- `sum_mul_log_eq_vonMangoldt` — **Halász's recursion** for completely multiplicative `f`:
  `∑_{m ≤ N} f(m) log m = ∑_{d ≤ N} Λ(d) f(d) ∑_{k ≤ N/d} f(k)`.

Both unconditional.

`RHTower.Mertens.log_summatory_eq` already had the constant-summand case (`∑_{m≤n} log m =
∑_{d≤n} Λ(d)⌊n/d⌋`), proved by counting multiples; `sum_divisors_swap` is the general form that
carries an arbitrary summand through the same reindexing, which is what a weighted sum needs.

The recursion is the identity the mean-value theory turns on: it expresses the log-weighted sum of
`f` through the *unweighted* sums of `f` over the shorter ranges `N/d`, and so converts information
about `f` at primes into information about its partial sums. Complete multiplicativity is used
exactly once, to split `f(m) = f(d) f(m/d)` — for merely multiplicative `f` the same shape holds
with `Λ` replaced by the Dirichlet inverse `f^{-1} * (f·log)`, which is not built here.

### Formal layer — the Möbius log recursion

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusLogRecursion.lean`.

- `one_pmul_log` — the logarithmic derivation kills the convolution identity.
- `moebius_pmul_log` — **`μ·log = −(Λ * μ)`**.
- `moebius_mul_log_apply` — pointwise: `μ(n) log n = −∑_{d ∣ n} Λ(d) μ(n/d)`.
- `sum_moebius_mul_log_eq` — **the recursion**:
  `∑_{m ≤ N} μ(m) log m = −∑_{d ≤ N} Λ(d) ∑_{k ≤ N/d} μ(k)`,
  the log-weighted Möbius sum expressed through the Mertens function on the ranges `N/d`.

All unconditional.

This is the identity these cards actually need. `sum_mul_log_eq_vonMangoldt` (previous section)
assumes complete multiplicativity, which **μ does not have** — `μ(4) = 0` while `μ(2)² = 1` — so it
does not apply to μ at all. The replacement is obtained by applying the logarithmic derivation to
`μ * ζ = 1`: the derivation kills the identity element, `ζ·log = log` and `μ * log = Λ`, giving
`(μ·log) * ζ = −Λ`, and multiplying by μ finishes.

`RHTower.pmul_log_mul` and `RHTower.zeta_pmul_log` (`DirichletLogDerivation.lean`, built for
Selberg's identity) supplied the derivation; only the Möbius specialisation was missing.

### Formal layer — Chebyshev's ψ through the Möbius function

`formal/GaloisForLFunctions/RHTower/Sieve/ChebyshevMoebius.lean`.

- `vonMangoldt_eq_sum_moebius_mul_log` — `Λ(n) = ∑_{d ∣ n} μ(d) log(n/d)`.
- `vonMangoldt_eq_sum_log_mul_moebius` — `Λ(n) = ∑_{d ∣ n} log d · μ(n/d)`.
- `sum_vonMangoldt_eq_moebius_logSummatory` — **`ψ(N) = ∑_{d ≤ N} μ(d) ∑_{k ≤ N/d} log k`**.
- `sum_vonMangoldt_eq_log_mertens` — **`ψ(N) = ∑_{d ≤ N} log d ∑_{k ≤ N/d} μ(k)`**.

All unconditional.

These are the two elementary bridges between the prime count and the Möbius function. The first
carries a cancellation hypothesis on μ into ψ (with Stirling controlling the inner log summatory);
the second carries prime information back to the Mertens function. Both are exact finite identities;
no estimate is made.

Corpus check: `RHTower.MobiusLogDivisorParaproduct` already applies `μ * log = Λ` but deliberately
keeps the result in *pair-labelled* antidiagonal form and never performs the reindexing, so the
summed identities above were absent. `RHTower.MoebiusFloorSummatory` already owns
`moebius_floor_summatory` (`∑_{d≤N} μ(d)⌊N/d⌋ = 1`) and `abs_sum_moebius_div_le_one`
(`|∑_{d≤N} μ(d)/d| ≤ 1`) — those were not rebuilt.

### Formal layer — the Euler product is damped by the distance

`formal/GaloisForLFunctions/RHTower/Sieve/EulerDamping.lean`.

- `norm_one_add_le_exp` — **`‖1 + z‖ ≤ exp(Re z + ‖z‖²)` for every complex `z`**, with no smallness
  hypothesis.
- `prod_norm_one_add_le_exp` — the product form over any finite index set.
- `sum_re_eq_sub_mulDistSq` — `∑_p Re(f(p)p^{−it}/p) = ∑_p 1/p − D(f,t;P)²`.
- `prod_euler_factor_le` — **`∏_{p∈P} ‖1 + f(p)p^{−it}/p‖ ≤ exp(∑_{p∈P}1/p + ∑_{p∈P}1/p² − D(f,t;P)²)`**.

All unconditional.

This is the structural reason Halász's theorem is stated in terms of `D`: the Euler product is below
its trivial size by exactly `exp(−D²)`, so a multiplicative function far from every character has a
small product, and the squared distance is the exponential rate.

The pointwise bound needs no hypothesis at all, which is worth recording since the textbook version
carries one. Squaring gives `‖1+z‖² = 1 + 2Re z + ‖z‖² ≤ 1 + 2Re z + 2‖z‖²`, and `1 + u ≤ exp u`
finishes — the discarded `‖z‖²` is precisely the slack that removes the usual `|z| ≤ 1/2`
restriction, so no series expansion of `log(1+z)` is required.

### Formal layer — the damped product as a Dirichlet sum

`formal/GaloisForLFunctions/RHTower/Sieve/EulerExpansion.lean`.

- `prod_one_add_eq_sum_powerset` — `∏_{p∈P}(1+z_p) = ∑_{T ⊆ P} ∏_{p∈T} z_p`.
- `primeFactors_prod_of_subset`, `prod_injOn_powerset` — on a set of primes, `T ↦ ∏_{p∈T} p` is
  injective (a subset is recovered as the prime factors of its product), so the subset sum is
  literally a sum over distinct squarefree `P`-smooth integers.
- `norm_sum_powerset_le_exp` — **`‖∑_{T⊆P} ∏_{p∈T} f(p)p^{−it}/p‖ ≤
  exp(∑_{p∈P}1/p + ∑_{p∈P}1/p² − D(f,t;P)²)`**.

All unconditional.

This converts the damping bound into a statement about a Dirichlet-type sum: a multiplicative
function far from every character has small partial sums over squarefree smooth numbers, at the
exponential rate `exp(−D²)`.

The estimate is not a triangle inequality. The sum is first rewritten *as* the product and only then
bounded, so no cancellation is discarded in the passage — a term-by-term bound on the same sum would
give `∏(1+1/p)`, with no dependence on the distance at all and hence no damping.

### Formal layer — the damped sum indexed by integers

`formal/GaloisForLFunctions/RHTower/Sieve/EulerIntegerIndex.lean`.

- `prod_eq_of_multiplicative` — `∏_{p∈T} f(p) = f(∏_{p∈T} p)` for multiplicative `f` on a finite set
  of distinct primes (induction, with pairwise coprimality from `Nat.coprime_primes`).
- `prod_term_eq` — the subset factor collapses to the integer term:
  `∏_{p∈T} f(p)p^{−it}/p = f(n) n^{−it}/n` with `n = ∏_{p∈T} p`.
- `norm_sum_smooth_le_exp` — **`‖∑_{n squarefree, P-smooth} f(n) n^{−it}/n‖ ≤
  exp(∑_{p∈P}1/p + ∑_{p∈P}1/p² − D(f,t;P)²)`**, the sum running over genuine distinct integers.

All unconditional.

The hypotheses are exactly multiplicativity (`f(ab) = f(a)f(b)` for coprime `a,b`), `f(1) = 1` and
`‖f‖ ≤ 1` — satisfied by μ, unlike the complete multiplicativity that the general Halász recursion
needs. Three separate facts are required to collapse a subset factor to an integer term:
multiplicativity across distinct primes, `log` additivity on the product, and `∏ 1/p = 1/n`; the
first is the only one that uses primality, via coprimality of distinct primes.

### Formal layer — the damping bound for μ itself

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusEulerDamping.lean`.

- `moebiusC`, `norm_moebiusC_le_one`, `moebiusC_one`, `moebiusC_mul_of_coprime`, `moebiusC_prime` —
  μ as a complex-valued function meets every hypothesis of the damped bound.
- `mulDistSq_moebiusC` — **`D(μ,t;P)² = ∑_{p∈P}(1 + cos(t log p))/p`**.
- `norm_sum_moebius_smooth_le_exp` — **`‖∑_{n squarefree, P-smooth} μ(n) n^{−it}/n‖ ≤
  exp(∑_{p∈P} 1/p² − ∑_{p∈P} cos(t log p)/p)`**.

All unconditional.

Because `μ(p) = −1` at every prime, the `∑_p 1/p` in the damping exponent cancels *exactly* against
the same term inside `D(μ,t;P)²`. What survives is the convergent `∑ 1/p²` against
`∑_p cos(t log p)/p`.

At `t = 0` this reads `exp(∑ 1/p² − ∑ 1/p)`, which tends to 0 as `P` exhausts the primes — the
elementary cancellation of μ over squarefree smooth numbers, with an explicit rate. This also marks
the boundary precisely: for `t ≠ 0` the bound is only as strong as a lower bound for
`∑_p cos(t log p)/p`, and supplying one uniformly in `t` is exactly the non-elementary input. The
formal layer now states the cards' obstruction as a single scalar quantity rather than as a citation.

### Formal layer — unconditional cancellation with an explicit rate

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusSmoothCancellation.lean`.

- `sum_inv_sq_le_two_of_pos` — `∑_{p∈P} 1/p² ≤ 2` for any finite set of positive integers.
- `norm_sum_moebius_smooth_le_exp_two` — **`‖∑_{n sf, P-smooth} μ(n)n^{−it}/n‖ ≤
  exp(2 − ∑_{p∈P} cos(t log p)/p)`**, with the `∑1/p²` clutter replaced by an absolute constant.
- `norm_sum_moebius_smooth_zero_le` — **`‖∑_{n sf, P-smooth} μ(n)/n‖ ≤ exp(2 − ∑_{p∈P} 1/p)`**.

All unconditional.

The `t = 0` statement is genuine unconditional cancellation with an explicit rate: since `∑_p 1/p`
diverges, the left side tends to zero as `P` exhausts the primes, and the rate is the prime harmonic
sum itself.

It also isolates what is *not* available. Nothing analogous follows here for `t ≠ 0`: the exponent is
governed by `∑_p cos(t log p)/p`, and a lower bound for that uniform in `t` is precisely the
non-elementary input these cards name as Menon 2026 / Matomäki–Radziwiłł. The gap is now a single
explicit scalar inequality rather than a literature citation.

`RHTower.Sieve.SquarefreeHarmonic.sum_inv_sq_le_two` supplied the telescoping bound; only the
restriction from `Icc 1 Y` to an arbitrary finite prime set was added.

### Formal layer — the cancellation in the limit

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusSmoothLimit.lean`.

- `tendsto_sum_primesBelow_inv_atTop` — the prime harmonic sum diverges, in `Finset` form
  (`∑_{p ∈ primesBelow N} 1/p → ∞`), obtained from mathlib's `not_summable_one_div_on_primes`.
- `tendsto_exp_two_sub` — `exp(2 − u) → 0` along any divergent `u`.
- `tendsto_norm_sum_moebius_smooth_zero` — **`‖∑_{n squarefree, p∣n ⇒ p<N} μ(n)/n‖ → 0`**.

All unconditional.

This is the limit form of the cancellation bound. The entire decay comes from the divergence of
`∑ 1/p` — no prime number theorem, no zero-free region.

Note what this does and does not give. The smooth-number restriction is essential: the statement is
about squarefree integers all of whose prime factors lie below `N`, not about `∑_{n ≤ N} μ(n)/n`,
which is a different (and already corpus-owned, `abs_sum_moebius_div_le_one`) quantity. The
corresponding limit at `t ≠ 0` remains out of reach from this chain, for the reason recorded above.

### Formal layer — at most one character can be close

`formal/GaloisForLFunctions/RHTower/Sieve/CharacterSeparation.lean`.

- `mulDistSqPair_comm` — the pairwise distance is symmetric.
- `mulDistSqPair_charFn` — **`D(n^{it}, n^{iu}; P)² = ∑_{p∈P}(1 − cos((t−u) log p))/p`**.
- `char_separation_of_close` — if `D(f, n^{it};P) ≤ δ` and `D(f, n^{iu};P) ≤ δ` then
  `D(n^{it}, n^{iu};P) ≤ 2δ`.
- `sum_one_sub_cos_le_of_close` — explicitly, **`∑_{p∈P}(1 − cos((t−u) log p))/p ≤ 4δ²`**.

All unconditional.

This is why a Halász-type argument only ever needs one distinguished frequency: the set of characters
within `δ` of a given `f` has diameter `2δ`, and `mulDistSqPair_charFn` converts that diameter bound
into a genuine constraint on `t − u`.

The hypothesis is only `‖f(p)‖ ≤ 1` — no multiplicativity — because the disc triangle inequality was
proved without it. This is where that earlier work pays: with only the unimodular version, the result
would not apply to μ.

### Formal layer — quantitative frequency separation

`formal/GaloisForLFunctions/RHTower/Sieve/FrequencySeparation.lean`.

- `two_div_pi_sq_mul_sq_le_one_sub_cos` — Jordan's inequality as `1 − cos x ≥ (2/π²)x²` on `|x| ≤ π`.
- `sq_mul_sum_sq_log_le_of_close` — **if `D(f, n^{it};P) ≤ δ` and `D(f, n^{iu};P) ≤ δ` and
  `|(t−u) log p| ≤ π` on `P`, then `(t−u)² ∑_{p∈P}(log p)²/p ≤ 2π²δ²`.**

Both unconditional.

This converts the qualitative uniqueness statement into a bound on the frequency itself: since the
weight `∑_p (log p)²/p` grows with `P`, the window of admissible `t − u` shrinks. A multiplicative
function cannot be close to two genuinely distinct characters, with an explicit rate.

The `|x| ≤ π` restriction is intrinsic, not an artefact — `1 − cos x` is periodic while `x²` is not,
so no inequality of this shape can hold globally. It is carried as a hypothesis on `P` rather than
silently assumed.

mathlib's `Real.cos_le_one_sub_mul_cos_sq` supplied the inequality; `Real.mul_le_sin` (Jordan) is
also present. Neither needed rebuilding.

### Formal layer — the Halász dichotomy

`formal/GaloisForLFunctions/RHTower/Sieve/HalaszDichotomy.lean`.

- `eq_of_both_close` — **uniqueness**: under the separation hypothesis, two frequencies both within
  `δ` of `f` are equal.
- `norm_sum_smooth_le_exp_of_far` — **damping**: a frequency at distance at least `δ` gives
  `‖∑_{n sf, P-smooth} f(n)n^{−it}/n‖ ≤ exp(∑_{p∈P}1/p + ∑_{p∈P}1/p² − δ²)`.

Both unconditional.

Together these are the dichotomy Halász's theorem rests on: for every frequency except at most one,
the Dirichlet sum is damped, and the bound away from the exceptional frequency is uniform in `t`.

What this does **not** do, stated plainly: it neither identifies the exceptional frequency nor gives
any lower bound on `δ`. Those are the analytic content, and no part of the elementary chain built
here supplies them. The formal layer now separates the two cleanly — the combinatorial/metric half is
complete and unconditional, and the remaining gap is exactly the analytic half named on these cards
as Menon 2026 / Matomäki–Radziwiłł.

### Formal layer — prime-power tail weights

`formal/GaloisForLFunctions/RHTower/Sieve/PowerWeightBound.lean`. First half of the explicit lower
bound for `∑_{p ≤ N}(log p)²/p`, which is what turns the frequency separation into a bound of the
shape `|t − u| ≲ δ/log N`.

- `sum_range_add_two_mul_half_pow` — the exact identity
  `∑_{j<M}(j+2)(1/2)^j = 6 − 2(M+3)/2^M`.
- `sum_range_add_two_mul_pow_le`, `sum_range_shift_pow_le` — **`∑_{k≥2} k x^k ≤ 6x²` for
  `0 ≤ x ≤ 1/2`**, so the proper prime powers of `p` contribute at most `6(log p)²/p²`.
- `log_sq_le_four_mul` — **`(log x)² ≤ 4x` for `x ≥ 1`**, via `log x ≤ 2√x`.

All unconditional.

The weight `k` (not just `x^k`) is forced by `log(p^k) = k log p`, which is why the ordinary
geometric series does not suffice. Together these give
`∑_{p^k ≤ N, k≥2} k(log p)²/p^k ≤ 24 ∑_{p ≤ √N} 1/p`, and with the corpus's
`HarmonicLogBound.sum_Icc_one_div_le_one_add_log` that is `O(log N)` — small against the main term
`½log²N` of `RHTower.abs_sum_vonMangoldt_log_div_sub_le`. The remaining step is the reindexing of
`∑_{m≤N} Λ(m)log m/m` into primes plus proper prime powers.

### Formal layer — the proper prime powers are a lower-order correction

`formal/GaloisForLFunctions/RHTower/Sieve/PrimePowerWeightTail.lean`.

- `sum_range_primePower_weight_le` — at a single prime,
  `∑_{j<M}(j+2)(log p)²/p^{j+2} ≤ 24/p`.
- `sum_primePower_weight_le` — **`∑_{p ≤ b} ∑_{j<M}(j+2)(log p)²/p^{j+2} ≤ 24(1 + log b)`**,
  uniformly in the number `M` of exponents allowed.

Both unconditional.

Combining last section's `∑_{k≥2} k x^k ≤ 6x²` at `x = 1/p` with `(log p)² ≤ 4p` gives `24/p` per
prime; the corpus's `HarmonicLogBound.sum_Icc_one_div_le_one_add_log` then sums it. Against the
`½log²N` main term of `abs_sum_vonMangoldt_log_div_sub_le` this `O(log N)` correction is lower order,
which is exactly what is needed to pass from `∑_{m≤N} Λ(m)log m/m` to `∑_{p≤N}(log p)²/p`.

The uniformity in `M` matters: no truncation of the exponent range is assumed, so the bound applies
whatever cutoff the reindexing later supplies. The remaining step is the support identification —
that the non-prime part of `Λ`'s support inside `Icc 1 N` embeds in `primesLE N ×ˢ range M` under
`(p,j) ↦ p^{j+2}`; `Sieve/PrimePowerSum.primePow_injOn` is the corresponding injectivity fact.

### Formal layer — separating the primes from their powers

`formal/GaloisForLFunctions/RHTower/Sieve/PrimeLogSqLower.lean`.

- `primePowShift_injOn` — `(p,j) ↦ p^{j+2}` is injective on `primesLE N ×ˢ range M`.
- `mem_image_of_nonprime` — every non-prime `m ≤ N` with `Λ(m) ≠ 0` is such a shifted prime power,
  with `j < Nat.log 2 N`.
- `sum_nonprime_vonMangoldt_log_div_le` — **`∑_{m ≤ N, m not prime} Λ(m)log m/m ≤ 24(1 + log N)`**.

All unconditional.

This is the support identification the previous section needed. `Λ(m) ≠ 0 ↔ IsPrimePow m`, and a
prime power that is not prime has exponent at least 2; the exponent bound `j < log₂N` comes from
`2^k ≤ p^k = m ≤ N`. With the injectivity, `Finset.sum_image` converts the sum over the image into
the double sum already bounded by `sum_primePower_weight_le`.

Combined with `RHTower.abs_sum_vonMangoldt_log_div_sub_le`
(`|∑_{m≤N} Λ(m)log m/m − ½log²N| ≤ 15 log N + 1`), the prime part now satisfies
`∑_{p≤N}(log p)²/p ≥ ½log²N − 39 log N − 25`: the weight in the frequency-separation bound grows like
`½log²N`, so the admissible window for `t − u` is `O(δ/log N)`.

### Formal layer — the explicit weight lower bound

`formal/GaloisForLFunctions/RHTower/Sieve/PrimeLogSqLower.lean` (capstone).

- `filter_prime_Icc_eq_primesLE` — `{m ∈ Icc 1 N | m.Prime} = primesLE N`.
- `sum_prime_log_sq_div_ge` — **`∑_{p ≤ N}(log p)²/p ≥ ½log²N − 39 log N − 25`**.

Unconditional.

This completes the four-part build begun with `PowerWeightBound`: split the `Λ·log/id` summatory at
`N`, identify the prime part as `∑_{p≤N}(log p)²/p`, bound the proper prime powers by `24(1+log N)`,
and read the main term off `RHTower.abs_sum_vonMangoldt_log_div_sub_le`.

Its purpose is to make `sq_mul_sum_sq_log_le_of_close` quantitative. That bound reads
`(t−u)² ∑_{p∈P}(log p)²/p ≤ 2π²δ²`; with the weight now known to grow like `½log²N`, the admissible
window is `|t−u| = O(δ/log N)` — the classical shape. No prime number theorem is used: the input is
Mertens-level, and every constant is explicit.

### Formal layer — the frequency window is O(δ / log N)

`formal/GaloisForLFunctions/RHTower/Sieve/HalaszWindow.lean`.

- `logSqWeight N := ½log²N − 39 log N − 25`.
- `sq_sub_mul_logSqWeight_le` — **`(t−u)² · logSqWeight N ≤ 2π²δ²`**.
- `sq_sub_le_div` — once the weight is positive, **`(t−u)² ≤ 2π²δ² / logSqWeight N`**.

Both unconditional.

This is the assembled quantitative uniqueness statement: two frequencies both within `δ` of the same
`f` in the multiplicative distance over the primes below `N` must satisfy `|t−u| = O(δ/log N)`.
Every constant is explicit, and the only arithmetic input is Mertens-level — no prime number theorem
and no zero-free region enter anywhere.

The elementary Halász layer for these cards is now complete end to end: distance geometry → disc
triangle inequality → Euler damping → integer indexing → μ instantiation → cancellation and its
limit → character separation → quantitative frequency separation → dichotomy → explicit window.

What is untouched, and cannot be reached from this chain, is the analytic half: identifying the
exceptional frequency and bounding `δ` from below. That is exactly the input these cards name as
Menon 2026 / Matomäki–Radziwiłł.

### Formal layer — window multiplicity and the trivial variance bound

`formal/GaloisForLFunctions/RHTower/Sieve/WindowMultiplicity.lean`. First step toward the
mean-square input `(6)`.

- `card_window_starts_le` — **`#{x < X : n ∈ (x, x+L]} ≤ L`**: a point is seen by at most `L` window
  starts, since `n ∈ (x,x+L] ⟺ n−L ≤ x < n`.
- `sum_window_sum_le` — exchanging the order of summation, `∑_x ∑_{n ∈ (x,x+L]} w(n) ≤ L ∑_n w(n)`
  for nonnegative `w`.
- `sum_normSq_window_le` — **`∑_{x<X} ‖∑_{x<n≤x+L} a_n‖² ≤ L² ∑_n ‖a_n‖²`**.

All unconditional.

This is the trivial variance bound that every short-interval argument improves on. Recording it fixes
the shape: the `L²` is `L` from Cauchy–Schwarz inside each window times `L` from the multiplicity of
starts, and it is the *multiplicity* count — not the Cauchy–Schwarz — that any saving must attack.
Menon's bound `(6)` is exactly the statement that for `a = μ` the true size is smaller by
`(log log L / log L)²`.

### Formal layer — the exact short-interval variance kernel

`formal/GaloisForLFunctions/RHTower/Sieve/WindowKernel.lean`.

- `windowOverlap X L n m := #{x < X : n, m ∈ (x, x+L]}`.
- `windowOverlap_eq_zero` — **the kernel vanishes when `|n − m| ≥ L`**.
- `windowOverlap_le` — `K(n,m) ≤ L`.
- `sum_window_pair_swap` — the double window sum equals the pair sum against `K`.
- `sum_normSq_window_eq` — **`∑_{x<X} ‖∑_{x<n≤x+L} a_n‖² = ∑_{n,m} K(n,m)·Re(a_n conj a_m)`**,
  an exact identity.

All unconditional.

Previous section gave the trivial bound; this replaces it by an equality. The substantive fact is the
support: both `n` and `m` lie in `(x,x+L]` only if `|n−m| ≤ L−1`, so short-interval variance is a
*local* problem — only pairs closer than `L` interact. This is the discrete counterpart of the Fejér
kernel's support, and it is what makes a correlation estimate for `μ(n)μ(m)` over near-diagonal pairs
the right target for `(6)`.

### Formal layer — the triangular (Fejér) weight

`formal/GaloisForLFunctions/RHTower/Sieve/WindowTriangularWeight.lean`.

- `windowOverlap_comm` — the kernel is symmetric.
- `windowOverlap_le_sub_dist` — **`K(n,m) ≤ L − |n − m|`**, the discrete triangular weight.
- `sum_normSq_window_le_triangular` — **`∑_{x<X} ‖∑_{x<n≤x+L} a_n‖² ≤
  ∑_{n,m} (L − |n−m|)‖a_n‖‖a_m‖`**.

All unconditional.

The kernel is exactly the discrete Fejér weight: `L` on the diagonal, decaying linearly, zero at
`|n−m| = L`. So the support statement of the previous section is the endpoint of a linear decay
rather than an isolated fact, and the constant-`L` bound is recovered only on the diagonal.

This completes the elementary framing of the mean-square input `(6)`: exact identity, symmetric
kernel, triangular bound, and the trivial `L²` estimate it improves. Any proof of `(6)` must exploit
cancellation in `∑_{n,m} (L−|n−m|) μ(n)μ(m)` over near-diagonal pairs — which is the analytic content
that remains open.

### Formal layer — the kernel bound is attained

`formal/GaloisForLFunctions/RHTower/Sieve/WindowKernelExact.lean`.

- `windowOverlap_eq_sub_dist` — **`K(n,m) = L − |n − m|`** whenever `|n−m| ≤ L` and the pair sits in
  the bulk (`L ≤ n, m ≤ X`), the common starts being exactly `[max(n,m) − L, min(n,m))`.
- `windowOverlap_self` — `K(n,n) = L` on the diagonal.

Both unconditional.

The triangular bound of the previous section is therefore an **equality** in the bulk, not merely a
valid estimate. This settles the accounting: the kernel side of the short-interval variance is exact,
so no sharpening is available there, and the whole of any improvement on the trivial `L²` bound must
come from arithmetic cancellation in the coefficients `μ(n)μ(m)`.

That is a negative result about method, and it is worth having explicitly: it rules out attacking
`(6)` by refining the geometry of the windows.

### Formal layer — reindexing the pair sum by the shift

`formal/GaloisForLFunctions/RHTower/Sieve/ShiftReindex.lean`.

- `sum_upper_triangle_eq_sum_shift` — **`∑_{n<m<R} F(n,m) = ∑_{1≤h<R} ∑_{n<R−h} F(n, n+h)`**, by the
  explicit bijection `(n,m) ↦ (m−n, n)` with inverse `(h,n) ↦ (n, n+h)`.
- `sum_pair_eq_diag_add_two_upper` — for symmetric real `W`,
  **`∑_{n,m<R} W(n,m) = ∑_n W(n,n) + 2∑_{n<m} W(n,m)`**.

Both unconditional.

Together these convert any symmetric pair sum into a diagonal term plus a sum of *shifted
correlations*. Applied to the triangular kernel this puts the short-interval variance in the form

`L ∑_n |a_n|² + 2 ∑_{h=1}^{L−1} (L−h) ∑_n Re(a_n conj a_{n+h})`,

which is the shape in which such a variance is actually estimated. For `a = μ` the diagonal term is
`L` times the squarefree count (density `6/π²`, already formalized in `Sieve/SquarefreeCount.lean`),
and the entire remaining question is cancellation in the shifted correlations `∑_n μ(n)μ(n+h)` — an
Elliott/Chowla-type input. This localises `(6)` precisely.

### Formal layer — the variance in autocorrelation form

`formal/GaloisForLFunctions/RHTower/Sieve/WindowAutocorrelation.lean`.

- `sum_pair_triangular_eq_autocorrelation` — **`∑_{n,m<R}(L−|n−m|)‖a_n‖‖a_m‖ =
  L∑_{n<R}‖a_n‖² + 2∑_{h≥1}(L−h)∑_{n<R−h}‖a_n‖‖a_{n+h}‖`**, an identity.
- `sum_normSq_window_le_autocorrelation` — the short-interval variance bounded in that form.

Both unconditional.

This is the terminus of the elementary reduction of `(6)`. The variance splits into a diagonal term
plus shifted correlations weighted by the same triangular factor `L − h`, hence supported on `h < L`.

The accounting is now complete and every piece is either done or identified:
the diagonal is `L` times the squarefree count (`Sieve/SquarefreeCount.lean`, density `6/π²`);
the kernel is exact (`WindowKernelExact`), so no saving is available from the geometry;
and the whole of the remaining problem is cancellation in `∑_n μ(n)μ(n+h)` for `1 ≤ h < L`.

That last item is an Elliott/Chowla-type correlation input — precisely what Menon 2026 /
Matomäki–Radziwiłł supply, and precisely what no elementary argument in this corpus reaches.

### Formal layer — the variance of μ is carried by the squarefree numbers

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusWindowVariance.lean`.

- `normSq_moebiusC_eq_indicator` — `‖μ(n)‖²` is the squarefree indicator.
- `sum_normSq_moebiusC_eq_card` — `∑_{n<R}‖μ(n)‖² = #{n < R : n squarefree}`.
- `sum_normSq_window_moebius_le` — **`∑_{x<X}‖∑_{x<n≤x+L}μ(n)‖² ≤ L²·#{n < X+L+1 : n squarefree}`**.

All unconditional.

Against the trivial `L²R` this saves the squarefree density `6/π²` (`squarefreeDensity_eq`), because
the support of μ is the squarefree set and nothing else.

Being precise about how small this gain is: it is a constant factor, not a saving in the `L` or `R`
dependence, and it is the *entire* unconditional improvement available from this direction. The
kernel was already shown exact, and the off-diagonal terms here are bounded only by their support.
Any further progress must come from cancellation in `∑_n μ(n)μ(n+h)` — which is the cited input.

### Formal layer — the variance against squarefree pair counts

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusPairVariance.lean`.

- `norm_moebiusC_eq_indicator` — `‖μ(n)‖` is the squarefree indicator.
- `sum_norm_moebiusC_shift_eq_card` — `∑_{n<R}‖μ(n)‖‖μ(n+h)‖ = P_h(R)`, the squarefree pair count.
- `sum_normSq_window_moebius_le_pairs` — **`∑_{x<X}‖∑_{x<n≤x+L}μ(n)‖² ≤ L·Q(R) + 2∑_{h≥1}(L−h)P_h(R)`**
  with `R = X+L+1`, `Q` the squarefree count and `P_h` the squarefree pair count at shift `h`.

All unconditional.

This is the sharpest form the elementary theory reaches, and it is worth stating exactly what it does
not do: **no cancellation between `μ(n)` and `μ(n+h)` is used anywhere.** Each off-diagonal term is
bounded by the size of its support alone. The triangular weight confines the sum to shifts `h < L`
and the diagonal is the squarefree count; everything else is the pair counts `P_h`, which are
*counts*, not cancelling sums.

Supplying that cancellation — a nontrivial bound for `∑_n μ(n)μ(n+h)` — is the single input the whole
reduction waits on, and it is exactly the published theorem these cards cite.

### Formal layer — a real window is an integer window

`formal/GaloisForLFunctions/RHTower/Sieve/RealWindow.lean`.

- `realWindow x L M` — the integers of `(x, x+L]` for a **real** start `x`.
- `realWindow_eq_Ioc` — **`realWindow x L M = Ioc ⌊x⌋ (⌊x⌋+L)`** for `x ≥ 0`.
- `sum_realWindow_eq` — hence the real-start window sum equals the integer-start sum at `⌊x⌋`.

Both unconditional.

This is the bridge between the cited estimates, which average over *real* starts with an integral
(`(1/Y)∫_Y^{2Y}|…|²dx`), and the discrete variance layer built above, which sums over integer starts.
The window sum is constant on each `[k, k+1)`, so the two formulations carry the same content and no
approximation is involved: `n > x ↔ ⌊x⌋ < n` and `n ≤ x+L ↔ n ≤ ⌊x+L⌋ = ⌊x⌋+L`.

Recording it matters because the discrete/continuous mismatch would otherwise be an unstated gap
between the formal layer and the statement of `(6)`/`(15)` on these cards.

### Formal layer — the integral over real starts is the discrete sum

`formal/GaloisForLFunctions/RHTower/Sieve/RealWindowIntegral.lean`.

- `floor_eq_of_mem_Ico`, `realWindow_const` — on `[k, k+1)` the real window *is* `(k, k+L]`.
- `integral_unit_window` — **`∫_k^{k+1} ‖∑_{x<n≤x+L} a_n‖² dx = ‖∑_{k<n≤k+L} a_n‖²`**.

Both unconditional.

This completes the bridge started in `RealWindow.lean`. The integrand is a step function: only the
right endpoint `x = k+1` sees a different window, and a single point is null, so the unit-interval
integral is exactly the value on the interior. Summing over `k` therefore turns the cited integral
mean square `(1/Y)∫_Y^{2Y}|…|²dx` into the discrete variance of the modules above, with **no error
term and no approximation**.

The discrete layer and the cited statement are now formally the same object, so the only remaining
gap on these cards is the arithmetic one — cancellation in `∑_n μ(n)μ(n+h)`.

### Formal layer — the continuous mean square IS the discrete variance

`formal/GaloisForLFunctions/RHTower/Sieve/WindowStepIntegral.lean`.

- `stepWindow c L k := ‖∑_{k<n≤k+L} c_n‖²`, and `stepWindow_floor_const` — the integrand `g ∘ ⌊·⌋`
  is constant on each **open** unit interval.
- `intervalIntegrable_stepWindow`, `integral_unit_stepWindow` — integrable, with
  `∫_k^{k+1} g⌊x⌋ dx = g k`.
- `integral_stepWindow_eq_sum` — **`∫_Y^{Y+K} g⌊x⌋ dx = ∑_{k<K} g(Y+k)`**.

All unconditional.

The bridge from `RealWindow.lean` is now complete in both directions: the mean square taken as an
integral over real starts — the form in which `(6)`/`(15)` are stated — equals the discrete variance
of the modules above **exactly**, with no error term.

The proof turns on using mathlib's *open*-interval congruences (`integral_congr_uIoo`,
`IntervalIntegrable.congr_uIoo`): the step function is constant precisely on `(k, k+1)` and jumps at
the right endpoint, so the open interval is the correct object and no null-set argument is needed.

### Formal layer — the bridge, stated for the real window

`formal/GaloisForLFunctions/RHTower/Sieve/RealWindowVariance.lean`.

- `integral_realWindow_eq_sum` — **`∫_Y^{Y+K} ‖∑_{x<n≤x+L} c_n‖² dx =
  ∑_{k<K} ‖∑_{Y+k<n≤Y+k+L} c_n‖²`**, for any cutoff `M > Y+K+L`.

Unconditional.

This states the bridge directly for the real-start window `(x, x+L]` rather than for the auxiliary
step function, so it is the identity the cited estimates `(6)`/`(15)` are literally about. The
hypothesis on `M` is only that every window met on `[Y, Y+K]` fits below the cutoff.

The short-interval layer is now closed as a chain of exact statements: continuous mean square =
discrete variance = pair sum against the overlap kernel = (kernel exact) triangular weight =
diagonal + shifted correlations, with the diagonal evaluated for μ as the squarefree count. The
single open link is arithmetic cancellation in `∑_n μ(n)μ(n+h)`.

### Formal layer — the trivial variance bound is attained

`formal/GaloisForLFunctions/RHTower/Sieve/WindowVarianceSharp.lean`.

- `sum_window_one` — every window of length `L` carries mass `L` for the constant sequence.
- `sum_normSq_window_one` — **`∑_{x<X} ‖∑_{x<n≤x+L} 1‖² = X·L²`**.

Unconditional.

The general bound gives `L²·(X+L+1)` for this sequence, so the two agree up to the boundary factor
`(X+L+1)/X → 1`. **No coefficient-free improvement of the trivial bound exists.**

This is the second no-go of the layer, and together with the exactness of the overlap kernel
(`WindowKernelExact`) it closes off the non-arithmetic routes completely: neither a sharper treatment
of the windows nor a better general inequality can help. Every remaining saving must come from
arithmetic cancellation in `∑_n μ(n)μ(n+h)`.

That is a useful negative result to have proved rather than assumed — it shows the cited input is
*necessary*, not an artefact of a lossy reduction.

### Formal layer — the variance *equals* the correlations

`formal/GaloisForLFunctions/RHTower/Sieve/WindowExactAutocorrelation.lean`.

- `re_mul_conj_comm`, `re_mul_conj_self` — the Hermitian pair weight is symmetric, and its diagonal
  is `‖a_n‖²`.
- `sum_normSq_window_eq_autocorrelation` — **an equality**:
  `∑_{x<X}‖∑_{x<n≤x+L} a_n‖² = ∑_n K(n,n)‖a_n‖² + 2∑_{h≥1}∑_n K(n,n+h)·Re(a_n conj a_{n+h})`.

Unconditional.

This upgrades the earlier autocorrelation *bound* to an identity. The previous version replaced
`Re(a_n conj a_{n+h})` by `‖a_n‖‖a_{n+h}‖` and so discarded every cancellation; here nothing is
discarded.

The consequence is a two-way statement rather than a one-way estimate: since `K` is `L` on the
diagonal and `L−h` at shift `h` in the bulk (`WindowKernelExact`), the short-interval variance is
**determined** by the shifted correlations — it is small exactly when `∑_n μ(n)μ(n+h)` cancels.
Small variance and correlation cancellation are the same statement, so the cited input is not merely
sufficient for `(6)`/`(15)`, it is equivalent to it.

### Formal layer — only the shifts below L matter

`formal/GaloisForLFunctions/RHTower/Sieve/WindowShiftRange.lean`.

- `windowOverlap_shift_eq_zero` — shifts `h ≥ L` contribute nothing.
- `sum_normSq_window_eq_autocorrelation_lt` — the identity with the correlation sum restricted:
  **`variance = ∑_n K(n,n)‖a_n‖² + 2∑_{h=1}^{L−1}∑_n K(n,n+h)·Re(a_n conj a_{n+h})`**.

Unconditional.

The number of correlations involved is `L − 1`, **independent of the averaging length `X`**. That is
what makes the reduction usable: a bound at the finitely many shifts `h < L` suffices, and no
statement about long-range correlations is needed.

Combined with the previous section, the position on these cards is now completely explicit. `(6)`/`(15)`
is *equivalent* to cancellation in the `L−1` shifted Möbius correlations `∑_n μ(n)μ(n+h)`,
`1 ≤ h < L`; the kernel weights are known exactly; and both non-arithmetic routes to a saving have
been ruled out by proof.

### Formal layer — the reduction as an implication

`formal/GaloisForLFunctions/RHTower/Sieve/CorrelationToVariance.lean`.

- `sum_normSq_window_le_of_correlation` — **if `|∑_n K(n,n+h)·Re(a_n conj a_{n+h})| ≤ δ` for every
  `1 ≤ h < L`, then `∑_{x<X}‖∑_{x<n≤x+L} a_n‖² ≤ L∑_n‖a_n‖² + 2Lδ`.**

Unconditional (as an implication).

This is the reduction in usable form. Everything to the left of the implication is proved: the exact
identity, the diagonal bound `K(n,n) ≤ L`, and the restriction to fewer than `L` shifts. Only the
hypothesis — the correlation estimate — is open, and it is exactly the published input these cards
cite.

Applied to `a = μ` with `Q` the squarefree count, a correlation bound `δ` yields
`variance ≤ L·Q + 2Lδ`, which is `(6)`/`(15)` once `δ` is of the required size. The elementary side of
these cards is therefore complete: no further unconditional work can shorten the gap, and the gap is
a single named hypothesis rather than a body of missing theory.

### Formal layer — the sign-count identity (14)

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusSignCount.lean`.

- `moebius_trichotomy` — `μ(n) ∈ {0, 1, −1}`.
- `moebius_eq_sub_indicator`, `moebius_sq_eq_add_indicator` — `μ = [μ=1] − [μ=−1]` and
  `μ² = [μ=1] + [μ=−1]`.
- `two_mul_card_moebius_eq_one`, `two_mul_card_moebius_eq_neg_one` — **equation (14)**:
  `#{n ∈ (t,t+L] : μ(n) = ±1} = (Q(t,L) ± M(t,L))/2`.

All unconditional.

Found by a numbered-statement audit of this card rather than by reading the Lean-status line: `(14)`
was not formalized anywhere in the corpus, although it is the step that converts the two summatory
estimates into the sign counts the theorem is about.

Its role is exactly the conversion the proof needs: a lower bound for `Q` (elementary, `(11)`/`(13)`,
already formalized) together with an upper bound for `|M|` (the cited input, `(6)`) bounds **both**
sign counts from below simultaneously. Without `(14)` the two estimates do not combine.

### Formal layer — both signs occur linearly often

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusSignLower.lean`.

- `card_moebius_sign_ge` — **if `Q(t,L) ≥ ½DL` and `|M(t,L)| ≤ ⅛DL` then both sign counts are at
  least `(3/16)DL`** — the conclusion of `(14)`.

Unconditional (as an implication).

This closes the `(14)` step of the proof. Its two hypotheses come from opposite sources: the lower
bound on `Q` is elementary sieve theory (`(11)`/`(13)`, formalized), and the upper bound on `|M|` is
the mean-square input `(6)` via Markov `(10)`. The sign-count identity is exactly what allows them to
be used together, and this lemma performs that combination.

The constant `3/16` is not sharp and the card says so; only its positivity is used downstream.

### Formal layer — counting a shifted congruence

`formal/GaloisForLFunctions/RHTower/Sieve/ShiftedCongruenceCount.lean`.

- `card_filter_dvd_add_shift` — `#{n ∈ (t,t+L] : M ∣ n+s} = #{m ∈ (t+s,t+s+L] : M ∣ m}`.
- `abs_card_filter_dvd_add_shift_sub_lt` — **the count differs from `L/M` by less than one,
  uniformly in the shift `s`**.

Both unconditional.

This is the second congruence a shifted correlation requires: `d² ∣ n` together with `e² ∣ n+h`. The
corpus already owned the unshifted sieve remainder bound (`Sieve/IntervalMultiples`); translating the
window rather than the modulus reduces the shifted case to it exactly, with no error term of its own.

Translation also avoids truncated subtraction entirely — the shifted window is `(t+s, t+s+L]`, never
a difference of naturals — which is what makes the reduction exact rather than approximate.

### Formal layer — the two congruences have a common solution

`formal/GaloisForLFunctions/RHTower/Sieve/JointCongruence.lean`.

- `negShift b h := (b − h % b) % b` — the natural representative of `−h` mod `b`.
- `negShift_add_dvd` — `b ∣ negShift b h + h` (axioms: `[propext]` only).
- `exists_joint_solution` — **for coprime moduli there is `n₀` with `a ∣ n₀` and `b ∣ n₀ + h`.**

Both unconditional.

A shifted correlation weighted by the squarefree identity `μ²(n) = ∑_{d²∣n} μ(d)` meets the pair of
conditions `d² ∣ n` and `e² ∣ n+h`. For coprime `d, e` the Chinese remainder theorem makes that pair
a single residue class, whose count in a window is then governed by the shifted-congruence bound of
the previous module.

One correctness note worth recording: the natural-number formula `b − h % b` is *not* the right
representative when `b ∣ h` (it gives `b`, not `0`), which is why `negShift` carries the outer `% b`.
The proof goes through `Nat.mod_add_mod` rather than assuming the two agree.

### Formal layer — the joint congruence is one residue class

`formal/GaloisForLFunctions/RHTower/Sieve/JointCongruenceClass.lean`.

- `joint_iff_dvd_shift` — for coprime moduli, **`a ∣ n ∧ b ∣ n+h ↔ ab ∣ n + negShift(ab) n₀`**,
  where `n₀` is any common solution.
- `abs_card_joint_sub_lt` — **the joint count in a window differs from `L/(ab)` by less than one**.

Both unconditional.

So the pair of conditions produced by expanding `μ²(n) = ∑_{d²∣n} μ(d)` on both `n` and `n+h` is no
harder to count than a single congruence: for coprime `d, e` the conditions `d² ∣ n` and `e² ∣ n+h`
cut out one class mod `d²e²`, counted with error below one uniformly in the shift `h` and the start.

Both directions of the equivalence run through `Nat.ModEq`, so no truncated natural subtraction
occurs anywhere — which is what keeps the statement exact rather than approximate. The positivity
hypothesis `0 < ab` is genuinely needed: at `a = 0` the modulus degenerates and the residue class
argument fails.

### Formal layer — the truncated pair sum as a weighted joint count

`formal/GaloisForLFunctions/RHTower/Sieve/TruncatedPairSwap.lean`.

- `sum_truncated_pair_eq` — **`∑_{n ∈ (t,t+L]} (∑_{d≤R, d²∣n} μ(d))(∑_{e≤R, e²∣n+h} μ(e))
  = ∑_{d,e≤R} μ(d)μ(e)·#{n ∈ (t,t+L] : d²∣n ∧ e²∣n+h}`**.

Unconditional, and exact — the exchange of summation incurs no error of its own.

With the previous module this assembles the two-variable sieve for a shifted correlation: the double
sum is reduced to joint counts, and each joint count with `gcd(d,e) = 1` equals `L/(d²e²)` to within
one, uniformly in `h` and `t`.

What is deliberately *not* claimed: the pairs with `gcd(d,e) > 1` are not evaluated here. Their
modulus is `lcm(d²,e²)` and solvability depends on whether the gcd divides `h`, so they need separate
treatment. The reduction above is exact regardless; only the evaluation of those terms is outstanding.

### Formal layer — the non-coprime pairs

`formal/GaloisForLFunctions/RHTower/Sieve/JointCongruenceEmpty.lean`.

- `gcd_sq_dvd_of_joint` — a common solution forces **`gcd(d,e)² ∣ h`**.
- `card_joint_eq_zero` — hence pairs with `gcd(d,e)² ∤ h` contribute **nothing**.
- `coprime_of_joint_of_squarefree` — **for squarefree `h`, every contributing pair is coprime.**

All unconditional.

This closes the gap flagged in the previous section. The non-coprime pairs are not evaluated but
*eliminated*: if `d² ∣ n` and `e² ∣ n+h` then `g = gcd(d,e)` satisfies `g² ∣ n` and `g² ∣ n+h`, so
`g² ∣ h`. The shift therefore decides which non-coprime pairs can occur at all, and when `h` is
squarefree only `g = 1` survives — so the truncated pair sum is entirely coprime and
`abs_card_joint_sub_lt` applies to every term.

The two-variable sieve for a shifted correlation is complete for squarefree shifts.

### Formal layer — the truncated squarefree pair count

`formal/GaloisForLFunctions/RHTower/Sieve/TruncatedPairCount.lean`.

- `abs_truncated_pair_sub_le` — for **squarefree** `h`,
  **`|∑_{n ∈ (t,t+L]} Q_R(n)Q_R(n+h) − L·∑_{d,e≤R, (d,e)=1} μ(d)μ(e)/(d²e²)| ≤ R²`**,
  uniformly in the start `t` and the shift `h`.

Unconditional.

This is the two-variable analogue of the corpus's `abs_truncated_squarefree_sub_le` and completes the
elementary sieve treatment of a shifted *squarefree* correlation: swap identity, elimination of the
non-coprime pairs, joint counts each accurate to within one, and `R²` pairs in total.

Scope, stated precisely: this evaluates the correlation of the **squarefree indicator** `μ²`, not of
`μ` itself. The `μ(d)μ(e)` appearing above are sieve coefficients, not values of the correlated
function. The genuinely open input remains cancellation in `∑_n μ(n)μ(n+h)`, where the signs of μ at
`n` and `n+h` must interact — something no counting argument reaches.

### Formal layer — the pair main term is bounded

`formal/GaloisForLFunctions/RHTower/Sieve/PairMainTermBound.lean`.

- `abs_main_pair_le` — **`|∑_{d,e≤R, (d,e)=1} μ(d)μ(e)/(d²e²)| ≤ 4`**, uniformly in `R`.

Unconditional.

With `abs_truncated_pair_sub_le` this makes the truncated pair sum `O(L) + O(R²)` with explicit
constants, and it does so **without evaluating the density as an Euler product** — the bound is just
`(∑_{d≤R} 1/d²)² ≤ 4`, using the corpus's `SquarefreeHarmonic.sum_inv_sq_le_two`.

Worth noting for what it avoids: the natural route to the pair density is
`∏_p(1 − 2/p²)` adjusted at primes with `p² ∣ h`, which needs infinite products and their
convergence. That is unnecessary for every use these cards make of the pair count, where only an
upper bound of the correct order is required.

### Formal layer — explicit upper bound for the truncated pair sum

`formal/GaloisForLFunctions/RHTower/Sieve/TruncatedPairUpper.lean`.

- `abs_truncated_pair_le` — for squarefree `h`,
  **`|∑_{n ∈ (t,t+L]} Q_R(n)Q_R(n+h)| ≤ 4L + R²`**, uniformly in `t`, `h` and `R`.

Unconditional, with both constants explicit.

This is the usable form of the two-variable sieve: a single inequality with no density constant to
evaluate and no hypothesis beyond squarefreeness of the shift. It follows from the pair count and the
main-term bound by the triangle inequality.

The seven-module shifted squarefree sieve is now complete and self-contained:
`ShiftedCongruenceCount` → `JointCongruence` → `JointCongruenceClass` → `TruncatedPairSwap` →
`JointCongruenceEmpty` → `TruncatedPairCount` → `PairMainTermBound` → this.

### Formal layer — assembling step 1 of the proof

`formal/GaloisForLFunctions/RHTower/Sieve/GoodStartCount.lean`.

- `card_le_good_add_bad` — **`#S ≤ #{good starts} + #Bad₁ + #Bad₂`**, where a start is *good* when
  both Möbius sign counts on `(t, t+L]` are at least `(3/16)DL`, `Bad₁` is where the Möbius sum
  exceeds `⅛DL`, and `Bad₂` is where the squarefree count falls below `½DL`.

Unconditional.

This assembles step 1 of the proof — `(10)`, `(13)` and `(14)` combined. The two exceptional sets
enter from opposite directions: `Bad₁` comes from the mean-square input through Markov, `Bad₂` from
the elementary squarefree count, and `card_moebius_sign_ge` converts a start outside both into one
carrying linearly many integers of each sign.

Phrased as a covering inequality in `ℕ` rather than a subtraction, so it composes with the
exceptional-set bounds without any truncation caveat.

### Formal layer — step 1 with the mean-square input as a hypothesis

`formal/GaloisForLFunctions/RHTower/Sieve/GoodStartMarkov.lean`.

- `card_le_good_add_meanSquare` — **`#S ≤ #{good starts} + V/(DL/8)² + #Bad₂`**, assuming only
  `∑_{t ∈ S} M(t,L)² ≤ V`.

Unconditional as an implication.

The hypothesis `hms` *is* the published mean-square input; everything else in the statement is
proved here — Markov via `RHTower.card_large_le_of_sum_sq_le`, the sign-count identity, and the
covering argument.

This is the form the cards' dependence should be read in: step 1 of the proof is a single theorem
whose only unproved ingredient is one named hypothesis. Supplying `V` of the size Menon's theorem
gives makes the exceptional term `o(#S)` and the conclusion is the card's `(14)` for almost every
start.

### Formal layer — equation (7), squarefree half; and an audit correction

`formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeIndicator.lean`.

- `filter_sq_dvd_eq_singleton` — at squarefree `n`, the only `d` with `d² ∣ n` is `d = 1`.
- `sum_moebius_sq_dvd_of_squarefree` — hence **`∑_{d² ∣ n} μ(d) = 1 = μ²(n)`** there.

Unconditional.

**Audit correction.** The Lean-status line above claims "the squarefree count `(7)`/`(11)`" is
formalized. That is accurate for `(11)` but not for `(7)`: `Sieve/SquarefreeCount.lean` works
throughout with the *truncated* sum `∑_{d ≤ R, d²∣n} μ(d)` and does not mention the predicate
`Squarefree` at all — the string does not occur in the file. The identity `μ²(n) = ∑_{d²∣n} μ(d)` is
absent from mathlib as well.

This module supplies the squarefree half. The complementary half — that the sum vanishes at
non-squarefree `n` — needs `{d : d² ∣ n}` identified with the divisors of the square part of `n`, and
is **not** proved here. It is recorded as outstanding rather than assumed.

### Formal layer — μ² is the squarefree indicator

Added to `formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeIndicator.lean`.

- `moebius_sq_eq_indicator` — **`μ(n)² = 1` exactly when `n` is squarefree, `0` otherwise.**
- `sum_moebius_sq_eq_card` — hence `∑_{n ∈ (t,t+L]} μ(n)² = #{n ∈ (t,t+L] : n squarefree}`.

Unconditional.

This supplies the *other* side of equation `(7)`. The identity `μ²(n) = ∑_{d²∣n} μ(d)` has two
halves, and the position is now exactly:

- `μ²(n) = squarefree indicator` — **proved** (this section);
- `∑_{d²∣n} μ(d) = 1` at squarefree `n` — **proved** (previous section);
- `∑_{d²∣n} μ(d) = 0` at non-squarefree `n` — **outstanding**; it needs `{d : d² ∣ n}` identified
  with the divisors of the square part of `n`.

`sum_moebius_sq_eq_card` is what lets the squarefree *count* `Q(t,L)` appearing in
`card_moebius_sign_ge` and `GoodStartMarkov` be written as a sum of `μ²`, which is the form the
sieve estimates produce.

### Formal layer — equation (7) is now complete

`formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeIndicatorZero.lean`.

- `sum_sq_dvd_eq_sum_squarefree` — the square-divisor sum may be restricted to squarefree `d`.
- `sum_moebius_sq_dvd_of_not_squarefree` — **the sum vanishes at non-squarefree `n`.**
- `moebius_sq_eq_sum_sq_dvd` — **equation `(7)`: `μ²(n) = ∑_{d²∣n} μ(d)`, for every `n ≥ 1`.**

All unconditional.

The outstanding half flagged in the previous section is closed, so the audit gap on `(7)` is
resolved and the status line above is now accurate.

The proof avoids factorisation entirely. Fix a prime `p` with `p² ∣ n`; on the squarefree `d` with
`d² ∣ n` the map `d ↦ d/p` (if `p ∣ d`) or `d ↦ dp` (otherwise) is an involution reversing the sign
of μ, so the sum cancels in pairs. Well-definedness needs only that `d² ∣ n` and `p² ∣ n` with
`p ∤ d` give `d²p² ∣ n` by coprimality — the square part of `n` is never constructed, and no
`Nat.factorization` machinery is used.

Restriction to squarefree `d` is essential rather than cosmetic: on `d` divisible by `p²` the map is
not an involution, and those terms are discarded first precisely because `μ` vanishes there.

### Formal layer — the truncation defect of the squarefree identity

`formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeTruncationDefect.lean`.

- `le_of_sq_dvd` — `d² ∣ n` with `n ≥ 1` forces `d ≤ n`.
- `abs_moebius_sq_sub_trunc_le` — **`|μ²(n) − ∑_{d ≤ R, d²∣n} μ(d)| ≤ #{d ∈ (R,M] : d² ∣ n}`**
  for `n ≤ M`.

Unconditional.

This is the bridge the corpus was missing between its two halves. `Sieve/SquarefreeCount.lean`
estimates the *truncated* sum `Q_R`, and `(13)` needs the *true* squarefree count `Q`; the defect
between them is now bounded pointwise by the count of omitted square divisors — which is exactly the
object `Sieve/AveragedSquarefreeTail.sum_tail_divisor_count_le` bounds on average over starts.

`le_of_sq_dvd` removes what would otherwise be a side condition: since `d² ∣ n` already forces
`d ≤ n`, the truncated sum is a genuine subsum of the full one for **every** `R`, with no hypothesis
relating `R` to `n`.

### Formal layer — the window truncation defect

Added to `formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeTruncationDefect.lean`.

- `abs_window_squarefree_sub_trunc_le` — **`|Q(t,L) − Q_R(t,L)| ≤ ∑_{d ∈ (R,M]} #{n ∈ (t,t+L] : d²∣n}`**
  for `t + L ≤ M`.

Unconditional.

The right-hand side is *exactly* the summand of `AveragedSquarefreeTail.sum_tail_divisor_count_le`,
so the two results now compose directly: summing over starts bounds the averaged defect by
`L·((B+L−A)/R + M)`, which is the card's `(12)`.

Chain for `(11)`–`(13)`, now complete and unconditional:
`(7)` `moebius_sq_eq_sum_sq_dvd` → pointwise defect → window defect (this) → averaged defect
(`sum_tail_divisor_count_le`) → Markov (`card_large_le_of_sum_sq_le`) → `(13)`. The corpus previously
had the two ends and neither of the two middle links.

### Formal layer — lower bound for the true squarefree count

Added to `formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeTruncationDefect.lean`.

- `squarefree_count_ge` — **`Q(t,L) ≥ D·L − (R + L/R) − defect(t)`**, where `D = squarefreeDensity`
  and `defect(t) = ∑_{d ∈ (R,M]} #{n ∈ (t,t+L] : d²∣n}`.

Unconditional.

This is the deterministic core of `(11)`–`(13)` for the **true** squarefree count, as opposed to the
truncated one: the sieve main term, its error `R + L/R`, and the truncation defect combined in a
single inequality, valid for every start with no exceptional set.

Only one step now separates it from `(13)`: the defect is `o(L)` for all but few starts, which is
Markov applied to `AveragedSquarefreeTail.sum_tail_divisor_count_le`. Both of those are already in
the corpus, so `Bad₂` in `GoodStartMarkov` is discharged by existing results rather than assumed.

### Formal layer — equation (13): the deficient starts are few

`formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeExceptional.lean`.

- `card_large_le_of_sum_le` — **Markov for a nonnegative quantity**: if the values sum to at most `V`,
  at most `V/θ` of them reach `θ`. (The corpus previously had only the mean-*square* form.)
- `card_squarefree_deficient_le` — **equation `(13)`**: the starts with
  `Q(t,L) < ½DL` number at most `V/θ`, where `θ = ½DL − (R + L/R)` and `V` bounds the summed
  truncation defect.

Both unconditional.

`Bad₂` in `GoodStartMarkov` is now supplied by a proved theorem rather than assumed. The elementary
half of step 1 is complete: `(7)` → truncation defect → `squarefree_count_ge` → `(13)`, with the
averaged tail (`AveragedSquarefreeTail`) providing `V`.

What remains hypothetical in step 1 is only `Bad₁`, which is the mean-square input `(6)`/`(15)` — as
the cards state.

### Formal layer — step 1, fully explicit

Added to `formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeExceptional.lean`.

- `card_le_good_add_explicit` — **`#S ≤ #{good starts} + V/(DL/8)² + W/θ`**, where
  `θ = ½DL − (R + L/R)`, `V` bounds the mean square of the Möbius sums, and `W` bounds the summed
  truncation defect.

Unconditional as an implication.

Both exceptional sets are now explicit, and the two hypotheses have different status: `hdef` (the
`W` bound) is elementary and supplied by `AveragedSquarefreeTail.sum_tail_divisor_count_le`, while
`hms` (the `V` bound) **is** the published mean-square input.

Step 1 of the Hall-law argument is therefore a single theorem with exactly one non-elementary
hypothesis, and that hypothesis is `(6)`/`(15)` verbatim. Everything else — the sign-count identity,
equation `(7)`, the truncated-to-true squarefree bridge, `(13)`, Markov in both the mean-square and
nonnegative forms, and the covering argument — is proved in the corpus.

### Formal layer — equation (13) with no free parameter

Added to `formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeExceptional.lean`.

- `card_squarefree_deficient_Ico_le` — **`#{t ∈ [A,B) : Q(t,L) < ½DL} ≤ L((B+L−A)/R + M)/θ`**,
  `θ = ½DL − (R + L/R)`.

Unconditional, with no free parameter: the averaged truncation tail
(`AveragedSquarefreeTail.sum_tail_divisor_count_le`) supplies the numerator directly.

This is the card's `(13)` in closed form. Combined with `card_le_good_add_explicit`, the *only*
remaining hypothesis anywhere in step 1 is the mean-square bound on the Möbius sums — the published
input. Every elementary ingredient is now a proved theorem with explicit constants.

Audit note: the same status-line overstatement found on the Hall-law card (claiming `(7)` proved)
also affected this card's `(20)`. Both are corrected above, and both statements are now genuinely
proved. Range citations such as "`(19)`-`(21)`" are what concealed the gap — the endpoints were
formalized and the middle statement was not.

### Formal layer — the kernel is constant on the bulk

`formal/GaloisForLFunctions/RHTower/Sieve/WindowKernelBulk.lean`.

- `windowOverlap_bulk` — at shift `h ≤ L`, **`K(n, n+h) = L − h`** for every start with `L ≤ n` and
  `n + h ≤ X`.
- `card_boundary_le` — fewer than `2L + 1` starts lie outside that bulk.

Both unconditional.

This is what makes the reduction usable with the literature's form of a correlation estimate. The
weighted sum `∑_n K(n,n+h)μ(n)μ(n+h)` appearing in the exact variance identity differs from
`(L−h)·∑_n μ(n)μ(n+h)` — the **unweighted** correlation that Chowla/Elliott-type results bound — by
at most `2L·L`, since the kernel is constant except on two boundary strips of fewer than `L` starts
each, where it never exceeds `L`.

So the hypothesis of `CorrelationToVariance.sum_normSq_window_le_of_correlation`, which is stated in
weighted form, can be discharged from an unweighted bound with an explicit `O(L²)` boundary loss.

### Formal layer — weighted correlation from unweighted

Added to `formal/GaloisForLFunctions/RHTower/Sieve/WindowKernelBulk.lean`.

- `abs_sum_kernel_sub_bulk_le` — for coefficients bounded by one,
  **`|∑_n K(n,n+h)c_n − (L−h)·∑_{bulk} c_n| ≤ (2L+1)·L`**.

Unconditional.

The remark of the previous section is now a theorem. The exact variance identity is stated with the
kernel weights, whereas Chowla/Elliott-type results bound the *unweighted* correlation
`∑_n μ(n)μ(n+h)`; this converts between them with an explicit `O(L²)` boundary loss, so the
hypothesis of `CorrelationToVariance.sum_normSq_window_le_of_correlation` can be discharged from a
literature-form bound.

Recorded because the two objects are genuinely different and the difference was previously
unexamined — the weighted form is what the identity produces, the unweighted form is what any
citable estimate would supply.

### Formal layer — the variance from an unweighted correlation bound

`formal/GaloisForLFunctions/RHTower/Sieve/UnweightedCorrelation.lean`.

- `sum_normSq_window_le_of_unweighted` — **`∑_{x<X}‖∑_{x<n≤x+L} a_n‖² ≤ L∑_n‖a_n‖² + 2L(Lε + (2L+1)L)`**
  from `|∑_{n ∈ bulk} a_n conj a_{n+h}| ≤ ε` at the shifts `1 ≤ h < L`, and nothing else.

Unconditional as an implication (axioms `[propext, Classical.choice, Quot.sound]`).

This is the reduction in the form a citable theorem can actually discharge. Earlier versions stated
the hypothesis in the kernel-weighted form the exact identity produces; no result in the literature is
phrased that way. Here the hypothesis is the plain correlation sum — what a Chowla/Elliott-type
estimate bounds — with the conversion cost `(2L+1)L` per shift carried explicitly rather than hidden.

The mean-square input `(6)`/`(15)` is therefore reduced, unconditionally and with explicit constants,
to a bound on the `L−1` unweighted shifted Möbius correlations.

### Formal layer — the Möbius mean square from a correlation bound

`formal/GaloisForLFunctions/RHTower/Sieve/MoebiusUnweighted.lean`.

- `re_moebiusC_mul_conj` — for the real-valued μ the Hermitian pair weight is the plain product
  `μ(n)μ(n+h)`.
- `sum_normSq_window_moebius_le_of_correlation` — **`∑_{x<X}‖∑_{x<n≤x+L} μ(n)‖² ≤
  L·#{n < X+L+1 : squarefree} + 2L(Lε + (2L+1)L)`** whenever `|∑_{n∈bulk} μ(n)μ(n+h)| ≤ ε` at the
  shifts `1 ≤ h < L`.

Unconditional as an implication.

This is the cards' mean-square input `(6)`/`(15)` stated for μ itself, reduced with explicit
constants to a bound on `L−1` shifted Möbius correlations — the exact statement a Chowla/Elliott-type
theorem provides. The diagonal is the squarefree count, already estimated elementarily.

The reduction is complete: no step between "correlations cancel" and "the mean square is small"
remains unproved.

### Formal layer — the multiplicity obstruction, quantified

`formal/GaloisForLFunctions/RHTower/Sieve/SquarefreeDivisorCount.lean`.

- `divisors_eq_image_powerset` — the divisors of a squarefree `m` are exactly the subset products of
  its prime factors.
- `card_divisors_of_squarefree` — **`#m.divisors = 2^{ω(m)}`.**

Unconditional.

This quantifies the obstruction the card states under "what is not claimed": `(3)` counts
representations, and a product with `ω(m)` prime factors admits `2^{ω(m)}` coprime factorizations.
Since `ω(m)` is unbounded, dividing a representation count by the multiplicity loses an unbounded
factor — so a representation density cannot by itself yield the `H/log x` distinct-target bound.

Together with `sum_uniform_booleanFactorization_signedPushforward` (the `2^{−ω}` normalization
reconstructs μ exactly, hence is circular), both halves of the card's hard gate are now formal
statements rather than prose: the naive multiplicity division is lossy, and the natural repair is
circular.

### Formal layer — the multiplicity is bounded *on average*

`formal/GaloisForLFunctions/RHTower/Sieve/AverageBalancedDivisors.lean`.

- `sum_card_divisors_window_le` — **`∑_{m ≤ X} #{d ∣ m : y ≤ d ≤ 2y} ≤ X · ∑_{y ≤ d ≤ 2y} 1/d`**.

Unconditional.

This is the other side of the obstruction, and it is the more useful one. Pointwise the multiplicity
`2^{ω(m)}` is unbounded (`card_divisors_of_squarefree`), but the right-hand side here is `≈ X log 2`,
so **on average a number has `O(1)` balanced divisors**.

The card's hard gate — converting representation density into a distinct-target bound — therefore
cannot be closed by a pointwise multiplicity division, but is not blocked by multiplicity on average.
Both facts are now theorems, which is what the gate needs stated precisely: the difficulty is the
*correlation* between having many balanced factorizations and being counted, not the average
multiplicity itself.

### Formal layer — the average multiplicity is at most two

Added to `formal/GaloisForLFunctions/RHTower/Sieve/AverageBalancedDivisors.lean`.

- `sum_inv_window_le_two` — `∑_{y ≤ d ≤ 2y} 1/d ≤ 2` for `y ≥ 1`.
- `sum_card_divisors_window_le_two` — **`∑_{m ≤ X} #{d ∣ m : y ≤ d ≤ 2y} ≤ 2X`.**

Unconditional, with an explicit constant and no logarithm.

So the average number of balanced divisors is at most `2` — not merely `O(1)`. The bound needs no
Mertens or harmonic asymptotics: every term of the reciprocal sum is at most `1/y` and there are
`y+1` of them.

Stated together, the two obstruction facts are now sharp:
pointwise multiplicity `2^{ω(m)}` (unbounded), average multiplicity `≤ 2`. Any route through
multiplicity must therefore exploit the distribution of `ω` on the counted set, not a worst-case or
an average bound alone.

### Formal layer — the second moment of the balanced divisor count

`formal/GaloisForLFunctions/RHTower/Sieve/BalancedDivisorSecondMoment.lean`.

- `sum_sq_card_divisors_window_le` — **`∑_{m ≤ X} (#{d ∣ m : y ≤ d ≤ 2y})² ≤
  X ∑_{d₁,d₂ ∈ [y,2y]} 1/lcm(d₁,d₂)`**.

Unconditional.

This is the quantity a Cauchy–Schwarz passage from representations to distinct images requires:
`#image ≥ (#representations)² / ∑ mult²`. Squaring the count turns a pair of divisibilities into a
single one by the least common multiple, and the Fubini exchange is then the same as for the first
moment.

It also shows where the `1/log x` in the card's target comes from. The first moment is bounded by a
constant (`≤ 2`), but `∑_{d₁,d₂ ∈ [y,2y]} 1/lcm(d₁,d₂)` carries a logarithm — so Cauchy–Schwarz
yields a distinct-image count smaller than the representation count by a factor `≍ log y`, which at
`y ≍ √x` is exactly the shape `(3)` needs.

### Formal layer — representations to distinct images

`formal/GaloisForLFunctions/RHTower/Sieve/ImageLowerBound.lean`.

- `sq_card_le_card_image_mul_sum_sq_fibre` — **`(#S)² ≤ #(image f) · ∑_t (#fibre t)²`.**
- `card_image_ge_of_sum_sq_le` — hence **`#(image f) ≥ (#S)²/V`** whenever the second moment of the
  fibre sizes is at most `V`.

Both unconditional.

This is the passage the hard gate asks for, in the abstract: a representation count plus a second
moment of the multiplicity bounds the number of *distinct* products from below. Nothing arithmetic
enters — only that the source set is the disjoint union of its fibres.

Combined with `sum_sq_card_divisors_window_le`, the route to `(3)` as a distinct-target statement is
now assembled up to one elementary evaluation: `∑_{d₁,d₂ ∈ [y,2y]} 1/lcm(d₁,d₂) ≍ log y`. With that,
`#distinct ≳ (#representations)²/(X log y)`, which at `y ≍ √x` is the card's target shape.

**Note this does not close the gate.** It gives a lower bound in terms of the representation count
and the multiplicity's second moment; whether the count surviving coprimality is large enough is the
remaining question, and it is not settled here.

### Formal layer — the gcd pair sum as a totient-weighted square

`formal/GaloisForLFunctions/RHTower/Sieve/GcdSumTotient.lean`.

- `divisors_gcd_eq_filter` — the common divisors of a pair, as a filtered interval.
- `sum_gcd_eq_sum_totient_mul_sq` — **`∑_{d₁,d₂ ∈ S} gcd(d₁,d₂) = ∑_{g ≤ M} φ(g)·(#{d ∈ S : g ∣ d})²`**,
  an identity.

Unconditional.

Since `1/lcm(d₁,d₂) = gcd(d₁,d₂)/(d₁d₂)`, this is the identity that evaluates the second moment of
the balanced divisor count. Applying `∑_{g ∣ n} φ(g) = n` at `n = gcd(d₁,d₂)` turns the pair sum into
a single sum over `g`, weighted by `φ(g)` and by the square of a multiple-count — and multiple-counts
in an interval are already bounded by `Sieve/IntervalMultiples`.

With `φ(g) ≤ g`, `#{d ∈ [y,2y] : g ∣ d} ≤ y/g + 1` and the corpus's harmonic bound, this yields
`∑_{d₁,d₂ ∈ [y,2y]} 1/lcm(d₁,d₂) = O(log y)` — the last elementary step of the Cauchy–Schwarz route
to a distinct-target count.

### Formal layer — reciprocal lcm reduced to gcd

Added to `formal/GaloisForLFunctions/RHTower/Sieve/GcdSumTotient.lean`.

- `inv_lcm_le_gcd_div` — `1/lcm(a,b) ≤ gcd(a,b)/y²` for `a, b ≥ y ≥ 1`.
- `sum_inv_lcm_le_gcd_sum` — **`∑_{d₁,d₂ ∈ [y,2y]} 1/lcm(d₁,d₂) ≤ y^{−2} ∑_{d₁,d₂} gcd(d₁,d₂)`.**

Both unconditional.

Via `gcd·lcm = ab` the reciprocal lcm is `gcd/(ab)`, and on the window `ab ≥ y²`. Chained with
`sum_gcd_eq_sum_totient_mul_sq`, the second moment of the balanced divisor count is now expressed
through `∑_g φ(g)·(multiple-count)²`, whose ingredients — `φ(g) ≤ g`, the interval multiple bound,
and the harmonic sum — are all corpus-owned.

The Cauchy–Schwarz route from representations to distinct targets is therefore complete as a chain of
proved reductions; what remains is arithmetic bookkeeping of the constants, not a missing step.

### Formal layer — the totient-weighted square sum, evaluated

`formal/GaloisForLFunctions/RHTower/Sieve/TotientSquareSum.lean`.

- `totient_mul_card_sq_le` — per modulus, `φ(g)·(#{d ∈ (a,b] : g ∣ d})² ≤ (b−a)²/g + 2(b−a) + g`.
- `sum_totient_mul_card_sq_le` — **`∑_{g ≤ M} φ(g)·(#{d : g ∣ d})² ≤
  (b−a)²(1 + log M) + 2(b−a)M + M²`.**

Both unconditional, with explicit constants.

This closes the arithmetic. Chaining the four results —
`sum_inv_lcm_le_gcd_sum` → `sum_gcd_eq_sum_totient_mul_sq` → this → `sum_sq_card_divisors_window_le`
→ `card_image_ge_of_sum_sq_le` — the second moment of the balanced divisor count over a dyadic window
is `O(y² log y)`, hence `∑ 1/lcm = O(log y)`, and the Cauchy–Schwarz distinct-image bound is fully
quantitative.

Every ingredient came from the corpus: the interval remainder bound (`Sieve/IntervalMultiples`),
`φ(g) ≤ g` (mathlib), and the harmonic bound (`Sieve/HarmonicLogBound`).

### Formal layer — the distinct-product bound for balanced pairs

`formal/GaloisForLFunctions/RHTower/Sieve/BalancedImageBound.lean`.

- `card_fibre_le_card_divisors` — each product fibre injects into the balanced divisors of the
  product: a pair `(d,e)` with `d ∈ [y,2y]` is determined by `d` and `de`.
- `card_image_mul_ge` — **`#{distinct products} ≥ (#S)²/V`** for any `V` bounding the second moment
  of the balanced divisor count.

Both unconditional.

This is the whole chain as a single usable theorem. Given a family `S` of balanced pairs with
products in `[1,X]`, it converts the **representation** count `#S` into a **distinct-product** count,
with `V = O(X log y)` supplied by `sum_sq_card_divisors_window_le` and the modules behind it.

The card's hard gate is therefore reduced to a size comparison: is `(#S)²/(X log y)` larger than the
Brun–Titchmarsh prime count of the same window? Every quantity in that comparison is now bounded by a
proved theorem; whether the inequality holds for the coprime-surviving `S` is the open question.

### Formal layer — the second moment with explicit constants

`formal/GaloisForLFunctions/RHTower/Sieve/SecondMomentExplicit.lean`.

- `Icc_eq_Ioc_pred` — the balanced window `[y,2y]` as the half-open `(y−1, 2y]`.
- `sum_inv_lcm_explicit` — **`∑_{d₁,d₂ ∈ [y,2y]} 1/lcm(d₁,d₂) ≤
  y^{−2}((y+1)²(1 + log 2y) + 2(y+1)(2y) + (2y)²)`**.

Unconditional, with every constant explicit — the right side is `O(log y)`.

The chain is now closed with no free parameters and no asymptotic notation:

`sum_inv_lcm_explicit` → `sum_sq_card_divisors_window_le` → `card_image_mul_ge`

gives `#{distinct products} ≥ (#S)² / (X · C(y))` with `C(y)` the explicit bound above.

The card's hard gate is a comparison between two computable quantities. Nothing structural remains
on this route; what is unresolved is whether the coprime-surviving representation count is large
enough, which the card states as its open question.

### Formal layer — the distinct-product bound, fully explicit

Added to `formal/GaloisForLFunctions/RHTower/Sieve/SecondMomentExplicit.lean`.

- `balancedMomentConst y := y^{−2}((y+1)²(1 + log 2y) + 2(y+1)(2y) + (2y)²)`.
- `sum_sq_card_divisors_explicit` — the second moment is `≤ X · balancedMomentConst y`.
- `card_image_mul_ge_explicit` — **`#{distinct products} ≥ (#S)² / (X · balancedMomentConst y)`**
  for any family `S` of balanced pairs with products in `[1,X]`.

Unconditional, one theorem, no free parameters.

This is the passage the card's hard gate asks for, stated as a single inequality between named
quantities. Given a lower bound on the coprime-surviving representation count `#S`, it delivers a
distinct-product count directly; `balancedMomentConst y = O(log y)` supplies the `1/log x` at
`y ≍ √x`.

The card's open question is now exactly: **is `(#S)²/(X · balancedMomentConst y)` larger than the
Brun–Titchmarsh prime count of the window?** No structural step is missing on this route, and the
collision normalization the card warns against is not used — only Cauchy–Schwarz on fibre sizes.

### Formal layer — counting integers of a prescribed Möbius sign

`formal/GaloisForLFunctions/RHTower/Sieve/CoprimeProductSign.lean`.

- `moebius_image_sign` — the product of a coprime pair carries the product sign: `μ(ab) = μ(a)μ(b)`,
  so a family whose factor signs multiply to `ε` produces products all with `μ = ε`. This is `(4)`.
- `card_moebius_eq_ge` — **`#{m ∈ [1,X] : μ(m) = ε} ≥ (#S)² / (X · balancedMomentConst y)`**.

Both unconditional.

This states the card's consequence in its intended form: a count of **integers of a prescribed
Möbius sign**, not of representations. The passage from `(3)` to `(4)` — which the card describes in
prose — is now a theorem, and it composes with the distinct-product bound without any further step.

What the theorem needs supplied is a lower bound on `#S`, the coprime-surviving balanced pairs with
a given product sign; that is what Matomäki–Radziwiłł's Theorem 2 provides via `(5)`–`(7)` and `(12)`.

### Formal layer — distinct-product local Hall capacity

The pipeline gate "distinct-product local Hall capacity" is now closed.
`RHTower/Sieve/BalancedHallCapacity.lean`:

`exists_hall_injection_balanced` — for a family `S` of balanced coprime pairs (first coordinate in
`[y, 2y]`, coprime, factor signs multiplying to `ε`) whose products all lie in a window
`(X, X+H]`, and a source set in the same window with

`#sources ≤ (#S)² / ((X+H)·balancedMomentConst y)`,

there is an `f` with `Set.InjOn f sources`, every `f n` a product of a pair of `S`, every
`μ(f n) = ε`, and `|f n − n| ≤ H`.

The capacity is the Cauchy–Schwarz distinct-product bound (`card_image_mul_ge_explicit`) applied on
the window, and the matching is `exists_injOn_displacement_le`; the sign clause is
`moebius_image_sign`.  So the capacity statement is *local*: it is about the products that actually
fall in the window, not about the global count.  Axioms:
`[propext, Classical.choice, Quot.sound]`.

What this does **not** supply is a lower bound for `#S` itself in a short window — that is the
all-interval coprime row supply the card obtains from the bilinear Möbius input, and it remains the
external ingredient.  The capacity theorem converts any such lower bound into an injection.

### Formal layer — co-moving sector flux was already formalized elsewhere

The "co-moving sector flux" gate was stale: the statement is owned by
`RHTower/MobiusBlockDefectEnergy.lean`, not by this card's own modules.

`abs_exp_zeroTotalSectorFluxCurrent_le_prefixEnergy` — for a zero-total increment sequence `d` and a
monotone representative mesh of width at most `h`,

`|∑_j d_j·exp(−x·r_j)| ≤ (∑_j (∑_{i≤j} d_i)²)^{1/2} · (∑_j (x·h·exp(−x·r_j))²)^{1/2}`,

i.e. Abel summation identifies the sharp-cutoff flux with the cumulative prefix, and Cauchy–Schwarz
pairs it against the Gibbs gradient.  Unconditional, axioms
`[propext, Classical.choice, Quot.sound]`.

Gate closed by reference, not by new work.  The remaining open item on this card is the analytic
theorem `(5)` — the all-interval coprime row supply — which depends on the external bilinear Möbius
input and is not reachable from the elementary layer.

### Toward the external input — `Sieve/RamareRoughBridge.lean`

Second step toward Matomäki–Radziwiłł Theorem 2.  Ramaré's identity produces a bilinear sum plus a
remainder carried by integers with no designated prime factor; that remainder is a *rough-integer*
sum, and the corpus already sieves those.  Joining the two closes the reduction:

- `primeFactorsIn_eq_empty_iff` — having no designated prime factor is having no designated prime
  divisor, which is exactly the predicate `card_rough_Ioc_le` bounds.
- `abs_sum_sub_ramare_le` — for `|f| ≤ B` on `S`, the difference between `∑_S f` and its Ramaré
  bilinear part is at most `B ·#{n ∈ S : no designated prime divisor}`.
- `abs_sum_sub_ramare_Ioc_le` — on an interval with designated primes all `p ≤ z`, that error is

  `B · ((b−a)·exp(c₁)/log z + (b−a)·exp(λc₂)(log z)^λ/λ^r + #truncDivisors(z#, r))`,

  the Brun bound, so of order `(b−a)/log z` at the usual parameter choice.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is the step that lets the bilinear method start: after it, a bounded sum over an interval *is*
its Ramaré bilinear part, to an error that vanishes relative to the interval length as `z` grows.
What follows in Matomäki–Radziwiłł — passing to Dirichlet polynomials and separating large values —
is where the corpus's existing `Dirichlet*` and `Halasz*` layers would attach; that junction is not
yet built.

### Toward the external input — `Sieve/RamareSquarePart.lean`

Third step.  In the bilinear sum an integer divisible by a designated prime `p` is written `n = p·m`,
and the factorization `f(p·m) = f(p)·f(m)` needs `p ∤ m`, i.e. `p² ∤ n`.  The integers failing this
are the multiples of `p²`, and they are provably few:

- `card_filter_sq_dvd_Ioc_lt` — their count in `(a,b]` is below `(b−a)/p² + 1`, from the corpus's
  exact interval-multiple count.
- `sum_card_filter_sq_dvd_le` — summed over designated primes in a range `(P₁, P₂]`, the total is at
  most `(b−a)/P₁ + #P`, using `sum_inv_sq_bigPrimeSet_le`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This isolates *why* the bilinear method designates primes from a high dyadic range rather than all
small primes: the obstruction to factorization is `(b−a)/P₁`, negligible only when `P₁` is large.
Together with `RamareRoughBridge` the two error terms of the decomposition — rough integers and
square-divisible integers — are now both bounded unconditionally, and they pull in opposite
directions in `z` and `P₁`, which is the tension the choice of ranges resolves.

### Toward the external input — `Sieve/RamareFactorization.lean`

Fourth step, and the one the previous two were error terms for.  Off the square-divisible integers
the designated prime splits multiplicatively:

- `coprime_div_of_not_sq_dvd` — `p` prime, `p ∣ n`, `p² ∤ n` gives `gcd(p, n/p) = 1`;
- `map_eq_mul_of_dvd_not_sq` — hence `f(n) = f(p)·f(n/p)` for any `f` multiplicative on coprime
  arguments (stated for a bare `f : ℕ → ℝ` with the coprime-multiplicativity hypothesis, so it
  applies to `μ`, `μ²`, and any `f` the method is run on);
- `sum_eq_mul_sum_image` — for a weight depending only on the cofactor,
  `∑_{n ∈ T} f(n)·g(n/p) = f(p) · ∑_{m ∈ T/p} f(m)·g(m)`, the map `n ↦ n/p` being injective on
  multiples of `p`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The bilinear sum is now genuinely bilinear: `∑_p f(p) · (cofactor sum)`, which is the shape the
mean-value and large-value theorems act on.  The four steps together — Ramaré identity, rough
remainder, square-divisible remainder, factorization — are the whole elementary half of
Matomäki–Radziwiłł's reduction.  What remains is the analytic half: Parseval/Perron to Dirichlet
polynomials, then the large-value separation, where the corpus's `Dirichlet*` and `Halasz*` layers
attach.

### Toward the external input — `Sieve/DirichletBilinear.lean`

The junction between the two halves, and it does fit.  The frequencies of `dirPoly` are logarithms,
so multiplying two polynomials adds the logarithms — that is, multiplies the underlying integers:

`dirPoly_mul` — `dirPoly N a t · dirPoly M b t = ∑_{j,k} a_j b_k exp(i t log((j+1)(k+1)))`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The Ramaré decomposition produces exactly a sum over pairs (designated prime, cofactor) weighted by
`f(p)·g(m)` — `sum_eq_mul_sum_image` puts it in that form — and this lemma says such a sum *is* the
product of the prime polynomial and the cofactor polynomial.  So the elementary half now lands on
the object the corpus's `DirichletMeanValue`, `DirichletLargeValues` and `FejerShortInterval` layers
already act on: `FejerShortInterval.norm_fejer_integral_sub_main_le` extracts the leading
coefficient of a `dirPoly` with error `∑ ‖a_n‖·4/(T log²(n+1))`, which is the coefficient-extraction
step the bilinear method needs after the product is formed.

Still to build: the Parseval/Perron passage that turns the *interval* sum into an integral of the
product over a bounded range of `t`, and the large-value separation that bounds that integral.  The
pieces exist separately; the chain from interval sum to Dirichlet integral is not yet assembled.

### Toward the external input — the product closes the loop

`dirPoly_mul_eq_dirPoly` (same module) upgrades the junction from an identity between two *shapes*
to an identity inside one class:

`dirPoly N a t · dirPoly M b t = dirPoly (N·M) (dirConv N M a b) t`,

where `dirConv N M a b r = ∑_{(j+1)(k+1) = r+1} a_j b_k` is the Dirichlet convolution.  The proof
groups the pair sum by the value of the product, using that a pair `(j,k)` has
`(j+1)(k+1) ≤ N·M`, so the fibres partition the index set; inside a fibre the exponential is
constant and factors out.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This matters because the corpus's analytic layers are stated for a single `dirPoly`, not for a
product: `FejerShortInterval.norm_fejer_integral_sub_main_le`, `DirichletMeanValue.dirichlet_meanValue`
and `DirichletLargeValues` all take one polynomial and its coefficient vector.  With the product
rewritten as `dirPoly (N·M) (dirConv …)` they apply to the Ramaré bilinear sum directly, with no new
analytic input.  The remaining gap is narrower than stated before: not "assemble a chain from
interval sum to Dirichlet integral", but supply the coefficient-size bounds on `dirConv` that those
theorems consume.

### Toward the external input — the coefficient bounds the analytic layer consumes

The gap named above is now filled.  `Sieve/DirichletBilinear.lean` gains:

- `prodIdx_val` and `filter_prodIdx_eq` — the convolution fibre is the fibre of the product index,
  stated once and reused;
- `norm_dirConv_le` — `‖dirConv N M a b r‖ ≤ ∑_{fibre} ‖a_j‖·‖b_k‖`;
- `sum_norm_dirConv_le` — `∑_r ‖dirConv N M a b r‖ ≤ (∑_j ‖a_j‖)·(∑_k ‖b_k‖)`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The second is the `ℓ¹` bound in the exact form the localisation error uses:
`FejerShortInterval.norm_fejer_integral_sub_main_le` bounds its error by
`∑ ‖a_n‖·4/(T log²(n+1))`, so a bound on `∑ ‖a_n‖` — with the `log²` factor only helping — is what
turns that theorem into a usable estimate for the Ramaré bilinear sum.

Status of this line: the elementary half of Matomäki–Radziwiłł's reduction is complete and
unconditional (Ramaré identity, rough remainder, square-divisible remainder, factorization), the
bilinear sum is identified with a single Dirichlet polynomial, and its coefficients are bounded in
`ℓ¹` by the two factor norms.  What is genuinely not built is the *analytic estimate* itself — the
large-value separation that beats the trivial bound.  That is the mathematical content of the
theorem, not plumbing, and the corpus's `DirichletLargeValues` layer has not been checked against
the parameter regime this application needs.

### Toward the external input — the large-values layer checked, and its input supplied

`DirichletLargeValues.largeValues_dirPoly` was checked against what this application produces.  It
is a δ-spaced mean-value bound,

`∑_r ‖dirPoly N a (λ_r)‖² ≤ (T + 4N(1+log N))·(1/δ + 2 log N)·∑_m ‖a_m‖²`,

with the counting form `card_largeValues_le` giving `(R+1)·V² ≤ (same)`.  It takes a *single*
`dirPoly` and the `ℓ²` norm of its coefficients — so after `dirPoly_mul_eq_dirPoly` it applies to
the Ramaré bilinear sum, provided the `ℓ²` norm of `dirConv` is available.  It now is:

`sum_norm_sq_dirConv_le` — `∑_r ‖dirConv N M a b r‖² ≤ D·(∑_j ‖a_j‖²)·(∑_k ‖b_k‖²)`, where `D`
bounds the fibres of the product index — that is, a divisor bound.  Cauchy–Schwarz inside each
fibre, then the fibrewise partition.  Unconditional, axioms
`[propext, Classical.choice, Quot.sound]`.

So both coefficient inputs the analytic layer consumes — `ℓ¹` for the localisation error, `ℓ²` for
the mean-value bound — are now proved for the convolution, in terms of the two factor norms and a
divisor bound.

The honest remaining item is unchanged and is the mathematics, not the interface: Matomäki–Radziwiłł
beat the trivial bound by exploiting that a *multiplicative* function's prime polynomial cannot be
large on many well-separated points.  Nothing in the corpus supplies that, and the `D` appearing
above is exactly where the divisor-function loss would have to be controlled.

### Toward the external input — the multiplicative ingredient the mean value cannot see

The step I recorded as missing above is partly in the corpus already, in the Halász layer, and it is
now in the form the large-values argument needs.  `Sieve/HalaszUniqueClose.lean`:

- `card_filter_close_le_one` — among a set of pairwise separated points, at most one is within
  Granville–Soundararajan distance `δ` of the multiplicative `f`.  Iterating `eq_of_both_close`,
  which says two close points coincide.
- `exists_subset_far` — hence there is an exceptional set `E` of at most one point with
  `δ < dist(f, χ_t)` for every `t ∈ S \ E`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is exactly what the mean-value theorem cannot supply.  `largeValues_dirPoly` holds for
arbitrary coefficients and is sharp for concentrated ones, so no argument through it alone can beat
the trivial bound; multiplicativity enters only through a statement of this kind.  With
`exists_subset_far` in hand, `HalaszDichotomy.norm_sum_smooth_le_exp_of_far` gives exponential decay
`exp(−δ²)` at every non-exceptional point.

What is still absent is the quantitative assembly: converting "far at all but one point" plus the
decay estimate into a bound on the full sum, with the exceptional point handled separately.  That
assembly is Halász's theorem proper, and the two corpus pieces are its endpoints rather than its
middle.

### Toward the external input — the Halász assembly

The quantitative assembly named as missing above is now built.  `sum_norm_smoothMulSum_le`
(same module): for `f` multiplicative with `‖f‖ ≤ 1`, primes `P`, and a set `S` of pairwise
separated points,

`∑_{t ∈ S} ‖smoothMulSum f P t‖ ≤ #S · exp(A − δ²) + exp(A)`,  `A = ∑_p 1/p + ∑_p 1/p²`.

Every point but one is far from `f`, so `norm_sum_smooth_le_exp_of_far` applies there and gives the
decayed bound; the single exceptional point takes the trivial bound `exp(A)`, which is
`norm_sum_smooth_le_exp` together with nonnegativity of the distance.  Unconditional, axioms
`[propext, Classical.choice, Quot.sound]`.

This is Halász's dichotomy in usable form: the whole sum over a separated set is controlled, with
the exceptional point isolated rather than assumed away.  Note what it does *not* claim — the decay
`exp(−δ²)` is only useful once `δ` is known to be large, and producing a lower bound for `δ` (the
"exceptional frequency" problem) is precisely the analytic half the corpus's Halász layer still
lacks.  The assembly makes that the single remaining input rather than one of several.

### Toward the external input — the distance `δ` made explicit

Halász's assembly needs `δ` large.  `Sieve/MoebiusDistance.lean` computes it for the Möbius case,
where `μ(p) = −1`:

- `mulDistSqPair_neg_one_charFn` — `D(μ, χ_t; P)² = ∑_{p ∈ P} (1 + cos(t log p))/p`, an identity.
- `mulDistSqPair_neg_one_zero` — at `t = 0` this is `2 ∑_{p ∈ P} 1/p`.
- `two_mul_logLog_sub_le_mulDistSqPair` — hence, by Mertens' second theorem,
  `2(logLog z − c) ≤ D(μ, χ_0; primesLE z)²`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

So at the trivial character the Möbius function is provably far, with distance growing like
`2 log log z`, and no analytic input is used.  For `t ≠ 0` the identity reduces the question to the
size of `∑_p cos(t log p)/p`; bounding that away from `−∑_p 1/p` is exactly a zero-free region for
`ζ`, i.e. the prime number theorem in disguise.

Checked, not assumed: mathlib carries Chebyshev-type bounds (`Mathlib/NumberTheory/Chebyshev.lean`,
upstreamed from PrimeNumberTheoremAnd) but not the prime number theorem — `tendsto_primeCounting`
only asserts `π → ∞`.  So the `t ≠ 0` half of the exceptional-frequency bound is not reachable from
mathlib as it stands, and the identity above is the correct place for a later attempt to start.

### Toward the external input — an elementary exceptional-frequency bound

The `t ≠ 0` half does *not* need the prime number theorem after all, if one asks only for a bound at
one of two frequencies.  Mertens' three-four-one device applies directly to the distance identity:

- `three_add_four_cos_add_cos_two` — `3 + 4cos x + cos 2x = 2(1 + cos x)² ≥ 0`.
- `two_mul_sum_inv_le_four_mul_dist_add_dist` —
  `2 ∑_p 1/p ≤ 4 D(μ, χ_t)² + D(μ, χ_{2t})²`, termwise from the identity.
- `two_mul_sum_inv_div_five_le_max` — hence
  `(2/5) ∑_p 1/p ≤ max(D(μ, χ_t)², D(μ, χ_{2t})²)`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`, and entirely elementary — the same
device that gives the classical zero-free region, but applied to the distance rather than to `ζ`,
so no analysis is involved.

With Mertens' second theorem this gives `max(D_t², D_{2t}²) ≫ log log z`: **the Möbius function is
far from at least one of any pair of characters `χ_t, χ_{2t}`**.  That is the exceptional-frequency
input Halász's assembly needs, in the only form elementary methods provide it.

What this does not give is a bound at a *prescribed* `t` — the pair `(t, 2t)` is disjunctive, and
turning it into a statement about every `t` individually is exactly where the zero-free region
becomes unavoidable.  So the correction to the note above is: the PNT is needed for the pointwise
statement, not for the disjunctive one, and the disjunctive one is now proved.

### Toward the external input — what the disjunctive bound is worth, checked

The disjunctive bound above was checked against the decay it is supposed to feed, and it is **not
sufficient**.  The corpus's Euler-product bound is

`‖smoothMulSum f P t‖ ≤ exp(S + S₂ − D(f, χ_t)²)`,  `S = ∑_p 1/p`, `S₂ = ∑_p 1/p²`,

so decay requires `D² > S + S₂`.  The three-four-one device gives only
`max(D_t², D_{2t}²) ≥ (2/5)S`, and `S + S₂ − (2/5)S = (3/5)S + S₂ > 0`: no decay.  The gap is not
an artefact of the constant — even the true value `D_t² = S + ∑_p cos(t log p)/p` for `t ≠ 0` leaves
`S + S₂ − D_t² = S₂ − ∑_p cos(t log p)/p`, so decay needs the *positivity* statement
`∑_p cos(t log p)/p > S₂`, not a size statement.  That is `log|ζ(1+it)|` bounded below, i.e. the
zero-free region again.

What survives unconditionally is the frequency-zero case, where the distance doubles:

`norm_smoothMulSum_zero_le` — `‖smoothMulSum μ P 0‖ ≤ exp(S₂ − S)`, which tends to zero.

Axioms `[propext, Classical.choice, Quot.sound]`.

So the honest position on this line: the elementary route reaches the frequency-zero cancellation and
the disjunctive distance bound, and stops there.  The corpus's Euler-product estimate is too lossy to
convert the disjunctive bound into decay, and Halász's actual argument avoids that estimate by
averaging over `t` rather than bounding pointwise.  A future attempt should replace the pointwise
Euler bound, not strengthen the distance bound.

### Toward the external input — the separation hypothesis made checkable

`card_filter_close_le_one` above took the separation condition as an abstract hypothesis
(`2π²δ² < (t−u)²·∑_p log²p/p`), which is awkward to verify at a call site.  The corpus's frequency
window removes that.

`card_filter_close_le_one_of_spacing` — if the points of `S` are pairwise at least `Δ` apart and
`2π²δ²/W < Δ²`, where `W = logSqWeight N` is the corpus's log-square weight, then at most one point
of `S` is within distance `δ` of `f`.  Proof: `HalaszWindow.sq_sub_le_div` bounds `(t−u)²` by
`2π²δ²/W` for two close points, contradicting the spacing.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is the usable form: `Δ` is the mesh of the frequency set one is working with, and `W` grows like
`(log N)²/2` by Mertens' first theorem, so the condition reads "the mesh exceeds the window width
`δ√(2π²/W)`" — a comparison between two explicit quantities rather than a hypothesis about the set.

### Toward the external input — the Halász interface in three forms

`Sieve/HalaszUniqueClose.lean` was refactored so the sum bound is proved once and specialised twice,
rather than restated:

- `sum_norm_smoothMulSum_le_of_card` — the bound given *any* proof that at most one point of `S` is
  close.  This is where the argument actually lives: far points take the decayed bound, the
  exceptional point takes the trivial one.
- `sum_norm_smoothMulSum_le` — the abstract-separation form, unchanged in statement.
- `sum_norm_smoothMulSum_le_of_spacing` — the checkable form: mesh `Δ`, window width from
  `logSqWeight N`, condition `2π²δ²/logSqWeight N < Δ²`.

All three axiom-clean, `[propext, Classical.choice, Quot.sound]`.

The Halász interface for this corpus is now complete in the sense that matters for reuse: a caller
supplies a frequency mesh and a distance, and gets a bound, with no hypothesis that needs unfolding
the definition of the distance.  The unresolved item remains the one recorded above — the pointwise
Euler-product estimate is too lossy at nonzero frequency, and replacing it with an average over `t`
is what Halász's theorem actually does.

### Toward the external input — first moment and large-value count

`Sieve/DirichletLargeValuesL1.lean` records the two forms of the mean-value bound the bilinear
method actually uses, neither of which is the mean square itself:

- `sum_norm_dirPoly_le_sqrt` — Cauchy–Schwarz on the corpus's mean-value theorem gives the *first*
  moment, `∑_r ‖F(λ_r)‖ ≤ √((R+1)·MV)`, which is the shape a coefficient extraction consumes.
- `card_largeValues_div_le` — dividing by `V²` gives the *count*:
  `R + 1 ≤ MV / V²` when `‖F(λ_r)‖ ≥ V` at every point.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

These are the last interface pieces on the analytic side.  The chain now reads, end to end and
unconditionally: bounded sum over an interval → Ramaré bilinear form (two sieve errors) →
factorization → single Dirichlet polynomial with `ℓ¹`/`ℓ²` coefficient bounds → first moment and
large-value count on a spaced frequency set → Halász dichotomy with a checkable spacing hypothesis →
the Möbius distance identity, with unconditional decay at frequency zero.

The single missing link, unchanged: at nonzero frequency the pointwise Euler-product bound does not
decay, and no distance estimate can repair it.  Everything on either side of that link is now built.

### Correction — mathlib does have the one-line nonvanishing

The note above ("mathlib carries Chebyshev bounds but not the prime number theorem") understated
what is available.  Mathlib proves `riemannZeta_ne_zero_of_one_le_re`: `ζ(s) ≠ 0` for `re s ≥ 1`
(`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`).  That is the analytically hard half of the
classical zero-free region, and it is present.  What is absent is the PNT asymptotic itself.

`Sieve/ZetaOneLineBound.lean` takes the first step toward using it:

`exists_pos_lower_bound_zeta_one_line` — for `0 < ε ≤ T` there is `c > 0` with
`c ≤ ‖ζ(1 + it)‖` for every `t ∈ [ε, T]`.  Continuity away from the pole plus nonvanishing on a
compact set.  Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

So the obstruction at nonzero frequency is now precisely: transfer this lower bound on `‖ζ(1+it)‖`
to a lower bound on the truncated sum `∑_{p ≤ z} cos(t log p)/p`.  That is the Euler product plus a
limiting argument — substantial, but no longer a missing *theorem*, only a missing *derivation*, and
the endpoints of the derivation are both formalized.

### Toward the external input — the Euler factor against its leading term

The derivation named above starts here.  `Sieve/EulerLogCompare.lean`:

- `norm_neg_log_one_sub_sub_self_le` — `‖−log(1 − w) − w‖ ≤ ‖w‖²/(2(1 − ‖w‖))`, from mathlib's
  `Complex.norm_log_one_add_sub_self_le` at `z = −w`.
- `norm_neg_log_one_sub_sub_self_le_sq` — hence `≤ ‖w‖²` as soon as `‖w‖ ≤ 1/2`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The relevance: `‖p^{-s}‖ = p^{-σ} ≤ 1/2` for every prime and every `σ ≥ 1`, so the Euler product
`exp(∑'_p −log(1 − p^{-s})) = ζ(s)` differs termwise from `∑'_p p^{-s}` by at most `p^{-2σ}`, and the
total discrepancy is under `∑_p p^{-2} < 1` — bounded, uniformly in the frequency `t`.  Taking real
parts, `log‖ζ(σ+it)‖` and `∑'_p cos(t log p)/p^σ` differ by `O(1)`.

That is the bridge between `ZetaOneLineBound` (a positive lower bound for `‖ζ(1+it)‖` on compact
frequency ranges) and the sum the Halász estimate needs.  What remains between them is the
summation bookkeeping — assembling the termwise bound into a `tsum` estimate, and the passage
`σ → 1⁺` — not any further analytic input.

### Toward the external input — the per-prime estimate, concretely

`Sieve/EulerLogCompare.lean` gains the two statements that make the quadratic bound apply to the
actual Euler factors:

- `norm_prime_cpow_neg_le_half` — `‖p^{-s}‖ ≤ 1/2` for every prime `p ≥ 2` and every `s` with
  `re s ≥ 1`.  Via `norm_natCast_cpow_of_pos`, then `(p:ℝ)^σ ≥ 2^σ ≥ 2`.
- `norm_euler_factor_sub_le` — hence `‖−log(1 − p^{-s}) − p^{-s}‖ ≤ ‖p^{-s}‖²`, uniformly over the
  half-plane `re s ≥ 1` and over all primes.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The `1/2` threshold is where the two halves meet: it holds for *every* prime at *every* `σ ≥ 1`
because the smallest prime is `2`, so no case analysis on `p` or on the frequency is needed anywhere
downstream.  The remaining bookkeeping is summing `‖p^{-s}‖² = p^{-2σ}` over primes — dominated by
`∑_n n^{-2}` — and the passage `σ → 1⁺`.

### Toward the external input — summability of the discrepancy

`Sieve/EulerLogCompare.lean` gains the summation side:

- `norm_prime_cpow_sq_eq` — `‖p^{-s}‖² = p^{-2σ}` as a real power.
- `summable_prime_norm_sq` — that family is summable over the primes whenever `re s ≥ 1`, by
  restriction of the `p`-series `∑_n n^{-2σ}` (convergent since `2σ ≥ 2 > 1`) along the injection
  `Nat.Primes ↪ ℕ`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

Together with `norm_euler_factor_sub_le` the discrepancy between the Euler logarithm and its leading
term is now a summable family with an explicit dominating series, so the `tsum` estimate

`‖∑'_p (−log(1 − p^{-s})) − ∑'_p p^{-s}‖ ≤ ∑'_p ‖p^{-s}‖²`

follows from the standard triangle inequality for sums.  That is the last piece of the bridge from
`ZetaOneLineBound` to `∑_p cos(t log p)/p^σ`; what remains after it is only the passage `σ → 1⁺`.

### Toward the external input — the tsum estimate assembled

`Sieve/EulerLogCompare.lean` now carries the comparison as a single statement:

- `summable_prime_cpow` — `∑'_p p^{-s}` converges absolutely for `re s > 1`.
- `summable_prime_euler_log` — so does `∑'_p −log(1 − p^{-s})`, since each term is within `‖p^{-s}‖²`
  of `p^{-s}`.
- `norm_tsum_euler_log_sub_tsum_le` — **the estimate**:

  `‖∑'_p (−log(1 − p^{-s})) − ∑'_p p^{-s}‖ ≤ ∑'_p ‖p^{-s}‖²`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

Combined with mathlib's `riemannZeta_eulerProduct_exp_log`, the left-hand sum *is* a logarithm of
`ζ(s)`, so this bounds the difference between `log ζ(s)` and `∑'_p p^{-s}` by a quantity under
`∑_n n^{-2} < 2` — uniformly in the frequency.  Taking real parts gives
`|log‖ζ(σ+it)‖ − ∑'_p cos(t log p)/p^σ| = O(1)`, which is the statement the Halász estimate needs.

The remaining step on this bridge is the passage `σ → 1⁺`, where `ZetaOneLineBound` supplies the
lower bound on `‖ζ(1+it)‖` over a compact frequency range.

### Toward the external input — zeta's logarithm equals the prime sum, up to `O(1)`

`Sieve/ZetaLogPrimeSum.lean` closes the analytic side of the bridge:

- `norm_riemannZeta_eq_exp_re` — from mathlib's `riemannZeta_eulerProduct_exp_log`,
  `‖ζ(s)‖ = exp(Re ∑'_p −log(1 − p^{-s}))`.
- `log_norm_riemannZeta_eq_re` — hence `log‖ζ(s)‖` *is* that real part.
- `abs_log_norm_riemannZeta_sub_tsum_re_le` — **the bridge**: for `re s > 1`,

  `|log‖ζ(s)‖ − ∑'_p Re(p^{-s})| ≤ ∑'_p ‖p^{-s}‖²`,

  and `Re(p^{-s}) = cos(t log p)/p^σ`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The right-hand side is under `∑_n n^{-2} < 2`, uniformly in the frequency `t`.  So the chain from
mathlib's nonvanishing theorem to the sum the Halász estimate consumes is complete on the open
half-plane: `ZetaOneLineBound` bounds `‖ζ(1+it)‖` below on a compact frequency range, and this bounds
`∑'_p cos(t log p)/p^σ` below in terms of it.

The one step still missing is the limit `σ → 1⁺` joining the two — an interchange of a limit with the
prime sum, not a new estimate.

### Toward the external input — the three-four-one weight at a prime

`Sieve/ZetaThreeFourOne.lean`:

- `re_prime_cpow_neg` — `Re(p^{-s}) = exp(−log p · σ)·cos(log p · t)`, from the `cpow`/`exp`
  definition and `Complex.exp_re`.  This is the identity that makes the prime sums trigonometric.
- `zero_le_three_four_one_term` — the Mertens weight of a single prime is nonnegative:

  `0 ≤ 3 Re(p^{-σ}) + 4 Re(p^{-σ-it}) + Re(p^{-σ-2it})`,

  because it factors as `p^{-σ}·2(1 + cos(t log p))² ≥ 0`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is the same device already applied to the Möbius distance, now applied to the Euler sums of
`ζ` where it does have teeth: summing over primes and feeding the result through
`abs_log_norm_riemannZeta_sub_tsum_re_le` gives the classical inequality on
`|ζ(σ)³ζ(σ+it)⁴ζ(σ+2it)|`, which is what forces a zero-free region rather than merely a disjunctive
bound.  The difference from the earlier attempt is the weight `p^{-σ}` in front: on the distance
side every prime carried weight `1/p` and the sum diverged; here the weight is summable and the
inequality survives the passage to `log‖ζ‖`.

### Toward the external input — the inequality summed over primes

`zero_le_three_four_one_tsum` (same module) sums the termwise weight:

`0 ≤ 3 ∑'_p Re(p^{-σ}) + 4 ∑'_p Re(p^{-σ-it}) + ∑'_p Re(p^{-σ-2it})`  for `σ > 1`.

Summability of each real-part family comes from `summable_prime_cpow_re`, obtained by pushing
`summable_prime_cpow` through `Complex.reAddGroupHom`; the three sums are then combined into one and
closed by `tsum_nonneg` on the termwise bound.  Unconditional, axioms
`[propext, Classical.choice, Quot.sound]`.

Combined with `abs_log_norm_riemannZeta_sub_tsum_re_le`, each prime sum is within `∑'_p ‖p^{-s}‖² < 2`
of the corresponding `log‖ζ‖`, so

`3 log‖ζ(σ)‖ + 4 log‖ζ(σ+it)‖ + log‖ζ(σ+2it)‖ ≥ −(3+4+1)·2 = −16`,

i.e. `|ζ(σ)³ ζ(σ+it)⁴ ζ(σ+2it)| ≥ e^{−16}` for every `σ > 1` and every `t`.  That is the classical
three-four-one inequality, with an explicit constant, and it is the standard starting point for a
quantitative zero-free region — the object this line has been missing.

### The three-four-one inequality for zeta, assembled

`three_four_one_log_zeta` (`Sieve/ZetaThreeFourOne.lean`) is the combination stated as one theorem.
For every `σ > 1` and every `t`, with `E = ∑'_p p^{-2σ}`:

`3 log‖ζ(σ)‖ + 4 log‖ζ(σ+it)‖ + log‖ζ(σ+2it)‖ ≥ −8E`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.  Printed statement checked against
the claim.

The proof is the two halves joined: `zero_le_three_four_one_tsum` makes the weighted prime sum
nonnegative, and `abs_log_norm_riemannZeta_sub_tsum_re_le` places each `log‖ζ‖` within `E` of its
prime sum — noting that `E` depends only on `σ`, since `‖p^{-(σ+it)}‖ = p^{-σ}`, so the same `E`
serves all three shifts.

This is the classical inequality behind the zero-free region, now unconditional in Lean with an
explicit constant and uniform in the frequency.  It is what the earlier disjunctive distance bound
could not deliver, and it is the object the Halász estimate needs at nonzero frequency.

### The inequality with a numeric constant

`tsum_prime_rpow_le` bounds the error term by `ζ(2)`: for `σ ≥ 1`,
`∑'_p p^{-2σ} ≤ π²/6`, comparing termwise with `1/n²` (rpow monotone in the exponent for base `≥ 1`)
and then injecting the primes into `ℕ` against mathlib's `hasSum_zeta_two`.

`three_four_one_log_zeta_const` — hence, for every `σ > 1` and every `t`,

`3 log‖ζ(σ)‖ + 4 log‖ζ(σ+it)‖ + log‖ζ(σ+2it)‖ ≥ −22`,

that is `|ζ(σ)³ ζ(σ+it)⁴ ζ(σ+2it)| ≥ e^{−22}`.  Unconditional, axioms
`[propext, Classical.choice, Quot.sound]`; printed statement checked.

The constant is crude — mathlib's only unconditional `π` bound at hand is `pi_le_four`, giving
`π²/6 ≤ 8/3` and `8·(8/3) < 22`, where the sharp form of the inequality has right-hand side `1`.
It is uniform in `t`, which is what the application needs; sharpening it is a matter of a better
numeric bound for `π`, not of the argument.

### The usable form, and where this line now stands

`log_norm_zeta_shift_ge` — upper bounds `A` at `σ` and `B` at `σ + 2it` give

`log‖ζ(σ+it)‖ ≥ (−22 − 3A − B)/4`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.  This is the shape a zero-free
region argument consumes: the pole at `σ → 1⁺` supplies `A ≈ log(1/(σ−1))`, a growth estimate in the
strip supplies `B ≈ log log t`, and the combination keeps `ζ(σ+it)` away from `0` in a region
`σ > 1 − c/log t`.

Built on this card's behalf, and now unconditional in the corpus:

| statement | content |
|---|---|
| `norm_euler_factor_sub_le` | Euler factor vs leading term, `≤ ‖p^{-s}‖²` |
| `norm_tsum_euler_log_sub_tsum_le` | the same, summed |
| `abs_log_norm_riemannZeta_sub_tsum_re_le` | `\|log‖ζ(s)‖ − ∑'_p Re(p^{-s})\| ≤ E` |
| `re_prime_cpow_neg` | `Re(p^{-s}) = p^{-σ} cos(t log p)` |
| `zero_le_three_four_one_tsum` | Mertens' weight, summed over primes |
| `three_four_one_log_zeta_const` | `\|ζ(σ)³ζ(σ+it)⁴ζ(σ+2it)\| ≥ e^{−22}` |
| `log_norm_zeta_shift_ge` | the rearranged, usable form |
| `exists_pos_lower_bound_zeta_one_line` | `‖ζ(1+it)‖` bounded below on compacts |

What is *not* built: the two growth estimates `A` and `B`.  Those are classical (the pole of `ζ` and
a convexity bound in the strip) and are the remaining input for a quantitative zero-free region —
which in turn is what the Halász estimate needs at nonzero frequency.

### Toward the external input — the real series near the pole

`Sieve/ZetaRealBound.lean` supplies the first of the two growth estimates the zero-free region needs:

- `antitoneOn_rpow_neg` — `x ↦ x^{-σ}` is antitone on the positives.
- `integral_rpow_neg_le` — `∫_1^N x^{-σ} dx ≤ 1/(σ−1)` for `σ > 1`, from mathlib's `integral_rpow`
  (using the `0 ∉ uIcc` branch, since the exponent is below `−1`).
- `tsum_nat_rpow_neg_le` — **the bound**: `∑'_n n^{-σ} ≤ 1 + 1/(σ − 1)` for `σ > 1`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The `1` is the `n = 1` term; the `n = 0` term vanishes by the `rpow` convention; the tail is dominated
by the integral through `AntitoneOn.sum_le_integral_Ico`.  This is the `A` of `log_norm_zeta_shift_ge`
once combined with `‖ζ(σ)‖ ≤ ∑'_n n^{-σ}`, giving `A ≈ log(1/(σ−1))` as required.

Remaining: the strip estimate `B`, a growth bound for `‖ζ(σ+2it)‖` in `t`.

### Toward the external input — the `A` bound, explicitly

`Sieve/ZetaRealBound.lean` completes the real-axis estimate:

- `norm_one_div_nat_cpow` — `‖1/n^σ‖ = n^{-σ}`, the `n = 0` term vanishing on both sides by the
  `cpow`/`rpow` conventions.
- `norm_riemannZeta_real_le` — `‖ζ(σ)‖ ≤ 1 + 1/(σ − 1)` for `σ > 1`, from mathlib's
  `zeta_eq_tsum_one_div_nat_cpow` and the series bound above.
- `log_norm_riemannZeta_real_le` — `log‖ζ(σ)‖ ≤ log(1 + 1/(σ − 1))`, using nonvanishing to know the
  norm is positive.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is the `A` of `log_norm_zeta_shift_ge` in closed form.  Substituting it,

`log‖ζ(σ+it)‖ ≥ (−22 − 3 log(1 + 1/(σ−1)) − B)/4`,

so a zero-free region now needs only `B`: an upper bound for `log‖ζ(σ+2it)‖` growing at most like
`log log t`.  That is the last classical input on this route.

### The trivial `B`, and why it is not enough

`norm_riemannZeta_le` — `‖ζ(s)‖ ≤ 1 + 1/(re s − 1)` for `re s > 1`, uniform in the imaginary part;
`log_norm_riemannZeta_le` is its logarithmic form.  Unconditional, axioms
`[propext, Classical.choice, Quot.sound]`.

Substituting both `A` and this `B` into `log_norm_zeta_shift_ge` gives

`log‖ζ(σ+it)‖ ≥ −22/4 − log(1 + 1/(σ−1))`,

i.e. `‖ζ(σ+it)‖ ≥ e^{−5.5}·(σ−1)/σ` — a genuine lower bound, but one that degenerates as `σ → 1⁺`.
**It therefore yields no zero-free region.**  It reproves only that `ζ` has no zero with `re s > 1`,
which the Euler product already gives.

This is the expected outcome and worth stating so the gap is not mistaken for arithmetic: the
classical argument needs `B` to come from the *analytic continuation* to `re s < 1`, where
`‖ζ(σ+2it)‖` grows like a power of `log t`, and where the lower bound at `σ+it` can then be pushed
left of `1`.  The trivial bound above lives entirely in the convergent half-plane and cannot see
that region.

So the remaining input on this route is precisely: a growth estimate for `ζ` in the strip
`0 < re s ≤ 1`.  Everything else in the classical zero-free region argument is now built.

### The `B` bound — growth of zeta in the strip

The corpus already owned the fractional-part continuation, so this needed no new analysis.
`RHTower/FractionalPartZeta.integral_Ioi_one_fract_cpow_of_re_pos` gives, for `re s > 0`, `s ≠ 1`,

`∫₁^∞ fract(t)·t^{-(s+1)} dt = 1/(s−1) − ζ(s)/s`.

`Sieve/ZetaStripGrowth.lean`:

- `norm_integral_fract_cpow_le` — the integral is at most `1/σ`, since `0 ≤ fract t < 1` and
  `∫₁^∞ t^{-σ-1} dt = 1/σ` (mathlib's `integral_Ioi_rpow_of_lt`).
- `norm_riemannZeta_strip_le` — **the bound**: for `re s > 0`, `s ≠ 1`,

  `‖ζ(s)‖ ≤ ‖s‖/‖s−1‖ + ‖s‖/re s`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is linear in `‖s‖`, hence `O(t)` on any vertical line in the strip — exactly the growth the
classical zero-free region argument consumes, and it holds *left* of the abscissa of convergence,
which the trivial bound of the previous section could not.

With it, all four inputs of the classical argument are in the corpus: the three-four-one inequality
with an explicit constant, the real-axis bound `A`, this strip bound `B`, and the interface
`log_norm_zeta_shift_ge` that combines them.  What remains is the optimisation — choosing
`σ = 1 + c/log t` and extracting the region — which is arithmetic on these four.

### Correction — a fifth input is needed, and the first half of it

The previous section said the remaining work was "arithmetic on these four".  That was wrong.  The
classical argument also needs to know that a hypothetical zero `β+iγ` forces `ζ` to be *small
nearby*: `‖ζ(σ+iγ)‖ ≤ (σ−β)·max‖ζ'‖`.  Without it the lower bound from three-four-one cannot be
contradicted, because nothing connects the value at `σ+iγ` to the zero.

`Sieve/ZetaDerivBound.lean` supplies the derivative half:

- `differentiableOn_riemannZeta_of_ne_one` — `ζ` is differentiable on any set avoiding the pole.
- `norm_deriv_riemannZeta_le` — **Cauchy's estimate**: `‖ζ'(c)‖ ≤ C/R` whenever `‖ζ‖ ≤ C` on the
  circle of radius `R` about `c` and the closed disc avoids `1`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.  With `norm_riemannZeta_strip_le`
supplying `C` on the circle, this bounds `ζ'` throughout the strip.

Still missing: the mean value step from `ζ'` to `ζ` along the segment from the zero.  An attempt
through `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` foundered on the `ℝ`-versus-`ℂ`
scalar restriction of the derivative; it was removed rather than left broken.  That step, plus the
final optimisation, is what remains.

### The fifth input, completed

`norm_riemannZeta_le_of_zero` (`Sieve/ZetaDerivBound.lean`) — if `ζ(z) = 0`, the segment from `z` to
`c` avoids the pole, and `‖ζ'‖ ≤ M` along it, then

`‖ζ(c)‖ ≤ M·‖c − z‖`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`; printed statement checked.

The earlier attempt failed on the `ℝ`-versus-`ℂ` scalar restriction of `fderiv`.  Parametrising the
segment by a real variable removes the difficulty entirely: `g t = ζ(z + t(c−z))` is a function
`ℝ → ℂ`, the chain rule is `HasDerivAt.scomp`, and the one-dimensional mean value inequality
`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` applies directly on `[0,1]`.

All five inputs of the classical zero-free region are now unconditional in the corpus:

| | |
|---|---|
| three-four-one | `three_four_one_log_zeta_const` |
| real-axis bound `A` | `log_norm_riemannZeta_real_le` |
| strip growth `B` | `norm_riemannZeta_strip_le` |
| derivative bound | `norm_deriv_riemannZeta_le` |
| small near a zero | `norm_riemannZeta_le_of_zero` |

What remains is the optimisation that combines them — choosing the radius, the offset `σ − 1`, and
the constant — to produce a region `σ > 1 − c/log t`.

### The five inputs combined

`Sieve/ZeroFreeCombination.lean`:

- `exp_le_norm_riemannZeta_shift` — for `σ > 1`, given only an upper bound `B₀` at `σ + 2it`,

  `‖ζ(σ+it)‖ ≥ exp((−22 − 3 log(1 + 1/(σ−1)) − log B₀)/4)`.

  An explicit *positive* lower bound off the real axis, from the three-four-one inequality and the
  real-axis bound.
- `le_mul_sub_of_riemannZeta_eq_zero` — a zero at `β + it` gives `‖ζ(σ+it)‖ ≤ M(σ−β)`, hence

  `exp((−22 − 3 log(1 + 1/(σ−1)) − log B₀)/4) ≤ M(σ − β)`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is the classical zero-free region argument reduced to a single inequality between explicit
quantities.  The free parameters are the offset `σ − 1`, the derivative bound `M` (from
`norm_deriv_riemannZeta_le` with `norm_riemannZeta_strip_le` on the circle), and `B₀` (from
`norm_riemannZeta_strip_le` at `σ + 2it`); all three grow only logarithmically or linearly in `t`,
so choosing `σ − 1 ≍ 1/log t` yields `β ≤ 1 − c/log t`.

Carrying out that choice — instantiating `M` and `B₀` and doing the calculus — is the remaining
step, and it is now genuinely arithmetic: no further property of `ζ` is required.

### The derivative bound, explicit

`norm_deriv_riemannZeta_le_explicit` (`Sieve/ZetaDerivBound.lean`) — for a disc of radius `R` about
`c` staying in the right half-plane (`R < re c`) and away from the real axis (`R < |im c|`),

`‖ζ'(c)‖ ≤ ((‖c‖ + R)/(|im c| − R) + (‖c‖ + R)/(re c − R))/R`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.  The two geometric hypotheses do
all the work: `R < |im c|` keeps the disc off the real axis, so it avoids the pole *and* gives
`‖w − 1‖ ≥ |im c| − R`; `R < re c` keeps it in the half-plane where the strip bound applies.

This makes the `M` of `le_mul_sub_of_riemannZeta_eq_zero` explicit in terms of the point alone.

**Note on strength.**  With this `M` and with `B₀` from `norm_riemannZeta_strip_le`, both grow
*linearly* in `|t|`, so the resulting region is of the shape `β ≤ 1 − c|t|^{-5/4}` — a genuine
zero-free region, but far weaker than the classical `1 − c/log|t|`.  The classical strength needs
`ζ(σ+it) ≪ log|t|` in the strip, which comes from the truncated Euler–Maclaurin expansion
(`ζ(s) = ∑_{n≤N} n^{-s} + N^{1-s}/(s−1) + O(|s|N^{-σ})` at `N ≍ |t|`), not from the single-term
fractional-part formula used here.  That sharpening is the natural next target.

### Correction — the linear strip bound gives **no** region at all

The note above said the current bounds yield a genuine but weak region `β ≤ 1 − c|t|^{-5/4}`.  That
is wrong; the arithmetic does not close.  Working it through with `σ = 1 + δ`:

- `B₀ ≤ 1 + 1/δ` at `σ + 2it` — this one is fine, and *logarithmic* once `δ ≍ 1/log|t|`, from the
  trivial bound `norm_riemannZeta_le`, since `re(σ+2it) = σ > 1`.
- `M ≈ C|t|` from `norm_deriv_riemannZeta_le_explicit`, because the segment to the zero reaches
  `re < 1` where only the linear strip bound applies.

The combination gives `σ − β ≥ e^{-5.5}(1 + 1/δ)^{-1}/(C|t|)`, and a region requires `σ − β > δ`,
i.e. `e^{-5.5} > C|t|(δ + 1)` — false for every large `|t|`, at every `δ`.  So no region follows.

The same computation shows what is needed: `M` must be at most a power of `log|t|`.  With the
classical `ζ ≪ log|t|` in the strip one gets `M ≪ log²|t|` and the optimisation closes.  A constant
loss like `e^{-22}` versus the sharp `1` is absorbable; a factor `|t|` is not.

**So the truncated Euler–Maclaurin expansion is not an optional sharpening — it is a required
input.**  What is built remains correct and reusable (the three-four-one inequality, the bridge, the
real-axis bound, Cauchy's estimate, the mean value step, and the combination); what is not yet built
is the one estimate that makes them bite.

### The required input — the truncated formula

The estimate identified as necessary above is now built, and again from corpus pieces rather than
from scratch.  `RHTower/ZetaPartialSumStrip.sum_cpow_sub_pow_eq` is the finite Abel identity and
`RHTower/FractionalPartZeta.integral_Ioi_one_fract_cpow_of_re_pos` the continuation; splitting
`∫_1^∞ = ∫_1^N + ∫_N^∞` and eliminating `∫_1^N` between them gives

`riemannZeta_eq_sum_add_tail` (`Sieve/ZetaTruncated.lean`) — for `re w > 0`, `w ≠ 1`, `N ≥ 1`:

`ζ(w) = ∑_{k ≤ N} k^{-w} + N^{1-w}/(w−1) − w ∫_N^∞ fract(t)·t^{-w-1} dt`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is the truncated Euler–Maclaurin expansion.  At `σ ≥ 1` and `N ≍ |t|` the three terms are
`O(log|t|)`, `O(1/|t|)` and `O(1)` respectively — so `ζ ≪ log|t|`, which is exactly the strength the
zero-free region needs and which the single-term formula could not provide.

The algebra was done by `linear_combination w * hcont − habel` with a `field_simp` normaliser; the
coefficients were derived by matching the `I₂` and `∑` terms rather than guessed.

### The logarithmic strip bound

`Sieve/ZetaTruncated.lean`:

- `norm_integral_Ioi_fract_cpow_le` — the tail beyond `N` is at most `N^{-σ}/σ`.
- `norm_riemannZeta_le_truncated` — **the bound**: for `re w > 0`, `w ≠ 1`, `N ≥ 1`,

  `‖ζ(w)‖ ≤ ∑_{k ≤ N} k^{-σ} + N^{1-σ}/‖w−1‖ + ‖w‖·N^{-σ}/σ`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`; printed statement checked.

Every term is elementary in `N` and `w`, and the three behave as advertised at `σ ≥ 1`, `N ≍ |t|`:
the sum is `O(log N)`, the middle term `O(1/|t|)`, the tail `O(1)`.  This replaces the linear strip
bound whose inadequacy was established two sections above, and it is the estimate the zero-free
region requires.

What remains is to instantiate `N` and combine: choosing `N = ⌈|t|⌉` turns this into
`‖ζ(σ+it)‖ ≤ C log|t|`, hence `M ≪ log²|t|` through the Cauchy estimate, at which point the
combination `le_mul_sub_of_riemannZeta_eq_zero` closes with `δ ≍ 1/log|t|`.

### `ζ ≪ log` in the strip — the required input, proved

`Sieve/ZetaTruncated.lean`:

- `sum_rpow_neg_le_harmonic` — for `σ ≥ 1`, `∑_{k ≤ N} k^{-σ} ≤ 1 + log N`, by comparison with the
  harmonic sum (the corpus already owned `sum_Icc_one_div_le_one_add_log`).
- `norm_riemannZeta_le_log` — **the bound**: for `re w ≥ 1`, `w ≠ 1`, and any `N ≥ max(1, ‖w‖)`,

  `‖ζ(w)‖ ≤ 2 + log N + 1/‖w − 1‖`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`; printed statement checked.

Taking `N = ⌈‖w‖⌉` this is `‖ζ(w)‖ ≤ 2 + log‖w‖ + 1/‖w−1‖`, i.e. **logarithmic in `|t|`** away from
the pole — the estimate whose absence was shown three sections above to break the entire zero-free
region argument.  Its ingredients were all already in the corpus: the finite Abel identity, the
fractional-part continuation, and the harmonic bound.

With it, `norm_deriv_riemannZeta_le_explicit` gives `M ≪ log²|t|` on a disc of fixed radius, and the
combination `le_mul_sub_of_riemannZeta_eq_zero` becomes satisfiable at `δ ≍ 1/log|t|`.

### Below the abscissa

`sum_rpow_neg_le_of_lt_one` (`Sieve/ZetaTruncated.lean`) — for `0 < σ < 1` and `N ≥ 2`,

`∑_{k ≤ N} k^{-σ} ≤ 1 + (N^{1-σ} − 1)/(1 − σ) + N^{-σ}`,

by the same antitone integral comparison used on the real axis, now with the `−1 < r` branch of
`integral_rpow`.  Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is what extends the logarithmic bound to the left of `re = 1`: at `σ = 1 − 1/log N` the factor
`N^{1-σ} = e` is bounded and `1/(1−σ) = log N`, so the sum is still `O(log N)` and the truncated
formula still gives `ζ ≪ log|t|`.  That is the region the Cauchy disc must reach in order to touch a
hypothetical zero, so this closes the last gap in the chain of estimates.

Remaining is the assembly: instantiating `N`, choosing the disc radius, and combining — arithmetic
on statements now all present.

### The bound left of the abscissa

`norm_riemannZeta_le_truncated_of_lt_one` — for `0 < re w < 1`, `w ≠ 1`, `N ≥ 2`,

`‖ζ(w)‖ ≤ (1 + (N^{1-σ} − 1)/(1 − σ) + N^{-σ}) + N^{1-σ}/‖w−1‖ + ‖w‖·N^{-σ}/σ`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.  At `σ = 1 − 1/log N` the first
group is `O(log N)` and the rest is `O(1)` once `N ≥ ‖w‖`, so `ζ ≪ log|t|` holds on a strip
extending to the left of `re = 1` — which is where the Cauchy disc must live.

The estimate side of the classical zero-free region is now complete in the corpus.  Every statement
it needs exists and is unconditional:

| | |
|---|---|
| three-four-one | `three_four_one_log_zeta_const` |
| real-axis `A` | `log_norm_riemannZeta_real_le` |
| `ζ ≪ log` at `σ ≥ 1` | `norm_riemannZeta_le_log` |
| `ζ ≪ log` at `σ < 1` | `norm_riemannZeta_le_truncated_of_lt_one` |
| Cauchy for `ζ'` | `norm_deriv_riemannZeta_le{,_explicit}` |
| small near a zero | `norm_riemannZeta_le_of_zero` |
| combination | `le_mul_sub_of_riemannZeta_eq_zero` |

What is left is the parameter optimisation, which requires no further property of `ζ`.

### The uniform sum bound across the abscissa

The two sum bounds (at `σ ≥ 1` and `σ < 1`) are now merged into one statement valid on both sides,
which is what a Cauchy disc straddling `re = 1` requires.

- `exp_sub_one_div_le` — `(e^u − 1)/u ≤ e` for `0 < u ≤ 1`, from `1 − u ≤ e^{-u}`.
- `sum_rpow_neg_le_uniform` — for `N ≥ 2`, `σ > 0` and `σ ≥ 1 − 1/log N`,

  `∑_{k ≤ N} k^{-σ} ≤ 2 + e·log N`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The `σ < 1` case is where the content is: writing `N^{1-σ} = e^{(1-σ)log N}` and using
`(1−σ)log N ≤ 1`, the quotient `(N^{1-σ} − 1)/(1 − σ)` is `log N·(e^u − 1)/u ≤ e·log N`, which stays
bounded as `σ → 1⁻` where the individual factors blow up.  That cancellation is exactly why the
truncated formula extends past the abscissa, and it is now proved rather than assumed.

### `ζ ≪ log` on a strip straddling the abscissa

`norm_riemannZeta_le_log_uniform` — for `re w ≥ 1/2`, `w ≠ 1`, `N ≥ 2`, `re w ≥ 1 − 1/log N` and
`‖w‖ ≤ N`,

`‖ζ(w)‖ ≤ 2 + e·log N + e/‖w − 1‖ + 2e`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`; printed statement checked.

The three ingredients are `sum_rpow_neg_le_uniform` for the sum, `N^{1-σ} ≤ e` and `N^{-σ} ≤ e/N`
for the other two terms — both from `(1 − σ)log N ≤ 1`, which is the same hypothesis that makes the
sum bound uniform.

Taking `N = ⌈‖w‖⌉`, this says `ζ ≪ log‖w‖` on the region
`{re w ≥ max(1/2, 1 − 1/log‖w‖)}` — a strip that reaches to the left of `1` by exactly the amount
the zero-free region argument needs, with the pole term `e/‖w−1‖` isolated.

This completes every estimate the classical argument uses.  What is left is the parameter
optimisation: choose the Cauchy radius, apply `norm_deriv_riemannZeta_le_explicit` with this bound
to get `M ≪ log²`, and close `le_mul_sub_of_riemannZeta_eq_zero` at `δ ≍ 1/log|t|`.

### `ζ' ≪ log` — the last estimate

`norm_deriv_riemannZeta_le_log` (`Sieve/ZetaDerivBound.lean`) — for a disc of radius `R` about `c`
with `1/2 ≤ re c − R`, `R < |im c|`, `1 − 1/log N ≤ re c − R` and `‖c‖ + R ≤ N`,

`‖ζ'(c)‖ ≤ (2 + e·log N + e/(|im c| − R) + 2e)/R`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

Cauchy's estimate with the uniform logarithmic bound on the circle.  The hypotheses are exactly the
geometry the zero-free region uses: the disc stays right of `1/2`, reaches no further left than
`1 − 1/log N`, avoids the real axis (hence the pole), and lies inside the truncation range.

At `R` fixed and `N ≍ |im c|` this is `‖ζ'‖ ≪ log|t|` — **not** the `log²|t|` quoted earlier, which
came from a cruder accounting; the sharper input makes the Cauchy estimate lose only the constant
`1/R`.  Either way it is polylogarithmic, which is what the combination needs.

The estimate side of the classical zero-free region is complete: three-four-one, the real-axis
bound, `ζ ≪ log` on a strip straddling the abscissa, `ζ' ≪ log` on the same region, the small-near-
a-zero step, and the combination.  Only the parameter optimisation remains.

### Correction — `M ≪ log²`, because the radius cannot be fixed

The remark just above, that the Cauchy estimate gives `‖ζ'‖ ≪ log|t|` "at `R` fixed", is wrong: `R`
cannot be fixed.  The disc must stay inside the region where the logarithmic bound holds, which
reaches only `1/log N` to the left of `re = 1`.  A point of the segment at `re = β` with `β` near `1`
therefore admits only

`R ≤ β − 1 + 1/log N`,

so `R ≍ 1/log N` when `β` is within `O(1/log N)` of `1` — which is precisely the case the argument is
about.  The `1/R` in Cauchy's estimate then contributes a second logarithm:

`M ≪ log N · (1/R) ≍ log² N`.

So the earlier statement `M ≪ log²|t|` was right and last section's revision of it was wrong.  This
does not change what is built or whether the argument closes — `log²` is polylogarithmic and the
combination still becomes satisfiable at `δ ≍ 1/log|t|` — but the mechanism matters for choosing the
parameters, since `R` and `δ` are tied to the same scale `1/log N`.

### The derivative bound in segment form

`norm_deriv_riemannZeta_le_log_of_re_ge` — a point `p` with `re p ≥ β` and `im p = γ` inherits

`‖ζ'(p)‖ ≤ (2 + e·log N + e/(|γ| − R) + 2e)/R`

under the same hypotheses on `β`, `R`, `N`, `γ`.  Unconditional, axioms
`[propext, Classical.choice, Quot.sound]`.

This is the form `norm_riemannZeta_le_of_zero` consumes: the segment from a zero `β+iγ` to `σ+iγ`
is horizontal, so every point on it has imaginary part exactly `γ` and real part at least `β`, and
the bound is therefore uniform along it with constants depending only on `β, γ, R, N`.

With this, the chain from "there is a zero at `β+iγ`" to the explicit inequality of
`le_mul_sub_of_riemannZeta_eq_zero` is a matter of choosing `R ≍ 1/log N`, `δ ≍ 1/log N` and
`N ≍ |γ|`, and checking the resulting numeric inequality.

### The zero-free inequality, assembled

`zero_free_inequality` (`Sieve/ZeroFreeAssembly.lean`) — given a zero `ζ(β+iγ) = 0`, a point
`σ + iγ` with `σ > 1`, a radius `R` with `1/2 + R ≤ β`, `1 − 1/log N ≤ β − R`, `R < |γ|`, `N ≥ 2`,
the segment inside the truncation range and off the pole, and any `B₀` bounding
`‖ζ(σ+2iγ)‖`:

`exp((−22 − 3 log(1 + 1/(σ−1)) − log B₀)/4) ≤ ((2 + e log N + e/(|γ| − R) + 2e)/R) · (σ − β)`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The proof is the two halves meeting: the segment from the zero is horizontal, so
`segment_re_im` gives every point real part `β + t(σ−β) ≥ β` and imaginary part exactly `γ`, hence a
uniform derivative bound; `norm_riemannZeta_le_of_zero` converts that into
`‖ζ(σ+iγ)‖ ≤ M(σ−β)`; and `le_mul_sub_of_riemannZeta_eq_zero` supplies the lower bound from
three-four-one.

Every quantity in the conclusion is elementary in `β, γ, σ, R, N, B₀`.  The classical zero-free
region is now the statement that these constraints are simultaneously satisfiable with
`R, σ−1 ≍ 1/log|γ|` and `N ≍ |γ|` — a numeric optimisation over six explicit parameters, with no
remaining input about `ζ`.

### What the assembled inequality yields — an arithmetic sketch, not yet formalized

Working the optimisation through (on paper; **not** in Lean, and after two earlier miscalculations,
so treat the exponent as provisional):

with `N ≍ |γ|`, `R ≍ 1/log N`, `M ≍ log²N`, and `B₀ ≍ e log N`, the left side of
`zero_free_inequality` is

`exp((−22 − 3log(1+1/δ) − log B₀)/4) ≈ e^{−5.5}·δ^{3/4}·(e log N)^{−1/4}`,

and the right side is `M(δ + (1−β))`.  Setting `1 − β = δ`, a contradiction needs

`δ^{−1/4} > 2C e^{5.5} e^{1/4} log^{9/4} N`,  i.e.  `δ < c·log^{−9} N`.

So the chain gives a zero-free region of the shape

`β ≤ 1 − c / log⁹|γ|`

— genuine, but weaker than the classical `1 − c/log|γ|`.  The loss is the crude Cauchy estimate for
`ζ'`: the classical proof bounds `ζ'/ζ` by Borel–Carathéodory and Hadamard factorisation, obtaining
`M ≍ log|t|` rather than `log²|t|`, and each power of `log` in `M` costs four in the exponent.

Two earlier claims in this file about this optimisation were wrong (one asserting `1 − c|t|^{-5/4}`,
one asserting no region at all); both came from fixing `δ ≍ 1/log|t|`, which is the classical scale
and far too large here.  The correct scale is `δ ≍ log^{-9}|t|`.  Nothing above depends on this
sketch — every Lean statement listed is proved independently of it.

### The zero-free statement

`riemannZeta_ne_zero_of_lt` (`Sieve/ZeroFreeAssembly.lean`) — the contrapositive of the assembled
inequality.  Under the same geometric hypotheses, if the explicit numeric comparison

`((2 + e log N + e/(|γ|−R) + 2e)/R)·(σ−β) < exp((−22 − 3log(1+1/(σ−1)) − log B₀)/4)`

fails to hold in the `≥` direction — that is, if the left side is strictly smaller — then

`ζ(β + iγ) ≠ 0`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is the form a region argument applies: everything about `ζ` is discharged, and what remains is
to choose `σ, R, N, B₀` as functions of `γ` so that the comparison holds.  The paper sketch above
indicates `δ = σ − 1 ≍ log^{-9}|γ|` is the right scale, giving `β ≤ 1 − c/log⁹|γ|`; that choice is
not yet formalized, and the sketch has been wrong before, so it is recorded as provisional.

### The lower bound as an explicit power

`exp_three_four_one_ge` — for `0 < δ ≤ 1` and `B₀ > 0`,

`e^{-11/2}·(δ/2)^{3/4}·B₀^{-1/4} ≤ exp((−22 − 3log(1+1/δ) − log B₀)/4)`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This removes the logarithms from the comparison the optimisation has to make: the left-hand side of
`riemannZeta_ne_zero_of_lt` need only be checked against `e^{-11/2}(δ/2)^{3/4}B₀^{-1/4}`, a product
of powers.  The `3/4` and `1/4` exponents are exactly the ones that make the classical optimisation
work, and they are now visible in a proved statement rather than only in the paper sketch.

With `B₀ ≍ e log N` and `M ≍ log²N`, the comparison to discharge becomes

`M·(δ + (1−β)) < e^{-11/2}·(δ/2)^{3/4}·(e log N)^{-1/4}`,

which at `1 − β = δ` reduces to `δ^{1/4} < c/log^{9/4}N` — the `log^{-9}` scale recorded above, now
derived from a proved inequality rather than an informal expansion.

### The practical entry point

`riemannZeta_ne_zero_of_lt_pow` — the zero-free statement with the logarithms eliminated.  Under the
geometric hypotheses, plus `σ − 1 ≤ 1` and `B₀ > 0`, if

`((2 + e log N + e/(|γ|−R) + 2e)/R)·(σ−β) < e^{-11/2}·((σ−1)/2)^{3/4}·B₀^{-1/4}`

then `ζ(β+iγ) ≠ 0`.  Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

Both sides are now elementary: a quotient of logarithms on the left, a product of powers on the
right.  Discharging it for a specific parameter family is arithmetic in `log N` alone.

State of this line: mathlib's Euler product and one-line nonvanishing → the three-four-one
inequality with explicit constant → the Euler-log bridge → `ζ ≪ log` and `ζ' ≪ log/R` on a strip
straddling the abscissa → Cauchy and mean value → the assembled inequality → this statement.
Sixteen modules, every theorem unconditional and axiom-clean.  What is not done is the choice of
parameters that discharges the final comparison, and the sketch indicating the resulting exponent
(`log^{-9}`) remains unformalized.

### The optimisation, algebraically

`lt_of_rpow_quarter_lt` — for `L, δ, C > 0`,

`δ^{1/4} < e^{-11/2}·2^{-3/4}·B^{-1/4}/(8CL²)`  ⟹  `8CL²δ < e^{-11/2}·(δ/2)^{3/4}·B^{-1/4}`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The `δ^{3/4}` common to both sides cancels, leaving a condition on `δ^{1/4}` alone.  **This is why
the scale is a fourth power**: the `L²` from the derivative bound sits against `δ^{1/4}`, so the
admissible `δ` is of order `L^{-8}` rather than `L^{-2}` — and with `L = log N` and the extra
`B^{-1/4} ≍ (log N)^{-1/4}`, of order `log^{-9}N`.  The exponent `9` from the earlier paper sketch
is now the direct consequence of a proved algebraic identity rather than an informal expansion.

What is still not formalized is the instantiation itself: choosing `δ`, `R`, `N` as functions of `γ`
and checking the hypothesis of this lemma holds.  That is arithmetic in `log N`, with every
inequality it needs already proved.

### The zero-free statement, optimisation-ready

`riemannZeta_ne_zero_of_quarter` — the composite.  Under the geometric hypotheses, plus

- `M ≤ 4CL²` (the derivative bound absorbed into a constant times `L²`),
- `σ − β ≤ 2(σ − 1)` (the zero is no further from `1` than the offset),
- `(σ−1)^{1/4} < e^{-11/2}·2^{-3/4}·B₀^{-1/4}/(8CL²)`,

it follows that `ζ(β+iγ) ≠ 0`.  Unconditional, axioms
`[propext, Classical.choice, Quot.sound]`.

Every hypothesis is now either geometric (disc placement, truncation range, segment off the pole) or
a comparison of explicit real quantities in `L`, `C`, `B₀`, `σ`, `β`.  **No analytic property of `ζ`
remains to be supplied.**

This is the natural stopping point for the chain: what is left is to exhibit functions
`σ(γ), R(γ), N(γ), C, L(γ)` satisfying the hypotheses for all large `|γ|`, which is a calculation in
`log|γ|` and involves no further mathematics about the zeta function.

### Scope of the zeta layer, stated plainly

This layer does **not** close the Matomäki–Radziwiłł gap these cards bottom out on, and should not be
read as doing so.  MR is a statement about *all* multiplicative `f` with `|f| ≤ 1` and about *every*
short interval; a zero-free region for `ζ` speaks only to `μ`, and only through PNT-type
consequences, which are far weaker than MR's short-interval strength.

What the layer is worth: it was the identified blocker for the Halász route at nonzero frequency
(the pointwise Euler bound does not decay there), it is classical mathematics the corpus did not
own, and every piece of it is unconditional.  A future session should treat it as infrastructure,
not as progress on `(5)`.

### The geometric hypotheses discharged

`geometric_of_close` — at radius `R = 1/(4 log N)` with `log N ≥ 3`, a zero satisfying
`1 − 3/(4 log N) ≤ β` automatically meets both disc conditions:

`1/2 + R ≤ β`  and  `1 − 1/log N ≤ β − R`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The second is an identity in disguise — `1/log N − 1/(4 log N) = 3/(4 log N)` — so the hypothesis
`1 − 3/(4 log N) ≤ β` is exactly what the strip condition needs, not a sufficient approximation to
it.  The first needs `log N ≥ 3` (so that `R ≤ 1/12` and `β ≥ 3/4`); an earlier attempt assumed only
`N ≥ 2` and was wrong, since `3/(4 log 2) > 1`.

This removes two of the hypotheses of `riemannZeta_ne_zero_of_quarter` for zeros in the range the
argument is about.  What remains to instantiate: `N` as a function of `γ`, the bound `M ≤ 4CL²`, the
`B₀` bound, and the quarter condition.

### The zero-free statement with the geometry discharged

`riemannZeta_ne_zero_of_close` — at radius `R = 1/(4 log N)`, for a zero within `3/(4 log N)` of `1`
and `log N ≥ 3`, the disc conditions are automatic and only the analytic-parameter comparisons
remain:

- `M ≤ 4CL²` with `M` the explicit derivative bound at this radius,
- `σ − β ≤ 2(σ−1)`,
- `(σ−1)^{1/4} < e^{-11/2}·2^{-3/4}·B₀^{-1/4}/(8CL²)`,
- the segment inside the truncation range and off the pole, and `B₀` bounding `‖ζ(σ+2iγ)‖`.

Then `ζ(β+iγ) ≠ 0`.  Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

Note the shape: the hypothesis `1 − 3/(4 log N) ≤ β` is the *assumption that the zero is close to
`1`* — which is what a zero-free region argument assumes for contradiction.  The conclusion then
says no such zero exists, provided the parameter comparisons hold.  So the remaining task is exactly
to choose `σ, N, C, L, B₀` as functions of `γ` making those comparisons true; the geometry no longer
participates.

### The derivative constant, absorbed

`deriv_const_le` — at radius `1/(4 log N)` with `log N ≥ 3` and `|γ| ≥ 1`, the explicit constant of
`norm_deriv_riemannZeta_le_log` satisfies

`(2 + e log N + e/(|γ| − 1/(4 log N)) + 2e)/(1/(4 log N)) ≤ 4·8·log²N`,

so `riemannZeta_ne_zero_of_close` can be instantiated with `C = 8`, `L = log N`.  Unconditional,
axioms `[propext, Classical.choice, Quot.sound]`.

The two hypotheses are what make the numerator linear in `log N`: `log N ≥ 3` lets the constants
`2 + 2e` be absorbed into `log N`, and `|γ| ≥ 1` keeps the pole term `e/(|γ| − R)` bounded (by
`12e/11`, since `R ≤ 1/12`).  The numeric step uses `Real.exp_one_lt_d9`.

With this, three of the remaining hypotheses of `riemannZeta_ne_zero_of_close` are discharged, and
the outstanding ones are the `B₀` bound at `σ+2iγ`, the truncation range condition, and the quarter
comparison — all in terms of `log N` and `σ − 1` alone.

### The bound at the doubled frequency

`norm_riemannZeta_double_le` — for `σ ≥ 1`, `|γ| ≥ 1`, `N ≥ 1` with `‖σ+2iγ‖ ≤ N`,

`‖ζ(σ+2iγ)‖ ≤ 5/2 + log N`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

`re(σ+2iγ) = σ ≥ 1` puts the point in the range of `norm_riemannZeta_le_log`, and the pole term is
harmless there: `‖σ+2iγ−1‖ ≥ |2γ| ≥ 2`, so `1/‖s−1‖ ≤ 1/2`.  This is `B₀`.

Of the hypotheses of `riemannZeta_ne_zero_of_close`, only two remain unsupplied: the truncation
range condition `‖·‖ + R ≤ N` along the segment, and the quarter comparison

`(σ−1)^{1/4} < e^{-11/2}·2^{-3/4}·(5/2 + log N)^{-1/4}/(8·8·log²N)`.

Both are inequalities in `log N` and `σ − 1` with no zeta content whatever.

### The truncation range condition

`segment_norm_le` — for `0 ≤ β ≤ σ ≤ 2`, `R ≤ 1` and `N ≥ 3 + |γ|`, every point of the segment
satisfies `‖·‖ + R ≤ N`.  Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The segment is horizontal with real part in `[β, σ] ⊆ [0,2]` and imaginary part `γ`, so
`‖·‖ ≤ 2 + |γ|` by `Complex.norm_le_abs_re_add_abs_im`; the hypothesis `N ≥ 3 + |γ|` then absorbs
`R ≤ 1`.

**Every hypothesis of `riemannZeta_ne_zero_of_close` is now discharged except one.**  With
`R = 1/(4 log N)`, `C = 8`, `L = log N`, `B₀ = 5/2 + log N`, `N ≥ 3 + |γ|`, `log N ≥ 3`, `|γ| ≥ 1`
and `1 < σ ≤ 2`, what is left is the single comparison

`(σ − 1)^{1/4} < e^{-11/2}·2^{-3/4}·(5/2 + log N)^{-1/4}/(64 log²N)`,

together with the segment avoiding the pole (immediate, since `|γ| ≥ 1`).  Choosing
`σ − 1 = c·log^{-9}N` for a small explicit `c` makes it true for large `N`; that final numeric step
is what remains.

### The quarter comparison holds at the `log^{-9}` scale

`quarter_comparison` — with `A = (e^{-11/2}·2^{-3/4}·2^{-1/4}/64)^4`, any `δ < A/L^9` satisfies

`δ^{1/4} < e^{-11/2}·2^{-3/4}·(5/2 + L)^{-1/4}/(64 L²)`

for every `L ≥ 3`.  Unconditional, axioms `[propext, Classical.choice, Quot.sound]`; supported by
`rpow_quarter_lt_of_lt_pow` (`δ < B⁴ → δ^{1/4} < B`).

The proof factors both sides as `(e^{-11/2}2^{-3/4})·X/(64L²)` and compares the middle factors:
`2^{-1/4}·L^{-1/4} = (2L)^{-1/4} ≤ (5/2 + L)^{-1/4}` since `5/2 + L ≤ 2L` at `L ≥ 3`.  **No largeness
beyond `L ≥ 3` is needed** — the constant `A` is absolute.

This is the last of the hypotheses of `riemannZeta_ne_zero_of_close`.  With
`δ = σ − 1 < A/log⁹N`, `R = 1/(4 log N)`, `C = 8`, `L = log N`, `B₀ = 5/2 + log N`, `N ≥ 3 + |γ|`,
`log N ≥ 3`, `|γ| ≥ 1`, every hypothesis is now discharged by a proved lemma — and the conclusion is
that `ζ` has no zero with `1 − 3/(4 log N) ≤ β` and `σ − β ≤ 2(σ−1)`.

### A zero-free region for `ζ`, unconditional

`riemannZeta_ne_zero_zero_free` (`Sieve/ZeroFreeAssembly.lean`) — with `A` the absolute constant
`(e^{-11/2}·2^{-3/4}·2^{-1/4}/64)^4`, if

- `log N ≥ 3`, `N ≥ 2`, `|γ| ≥ 1`, `N ≥ 3 + |γ|`, `‖σ+2iγ‖ ≤ N`,
- `1 − 3/(4 log N) ≤ β`, `0 ≤ β ≤ σ`, `1 < σ ≤ 2`, `σ − β ≤ 2(σ−1)`,
- `σ − 1 < A / log⁹N`,

then `ζ(β + iγ) ≠ 0`.  Unconditional, axioms `[propext, Classical.choice, Quot.sound]`; printed
statement checked.

Every hypothesis is arithmetic in `N, |γ|, β, σ` — all the analytic content sits in the lemmas
above, and the segment's avoidance of the pole is derived from `|γ| ≥ 1` rather than assumed.

Read as a region: taking `N = ⌈3 + |γ|⌉` and `σ = 1 + A/(2 log⁹N)`, the hypotheses hold for `|γ|`
large, and the conclusion denies zeros with `β` in the stated range.  The `log^{-9}` scale is the
one predicted by the earlier sketch and confirmed independently by `lt_of_rpow_quarter_lt`; it is
weaker than the classical `log^{-1}` because the derivative bound comes from Cauchy's estimate
rather than Borel–Carathéodory.

### The constant, named and bounded

`zeroFreeConst := (e^{-11/2}·2^{-3/4}·2^{-1/4}/64)^4`, with `zeroFreeConst_pos` and
`zeroFreeConst_le_one` proved.  Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

Both facts are needed to read the theorem as a region: positivity makes the excluded strip nonempty,
and `≤ 1` lets `σ = 1 + zeroFreeConst/(2 log⁹N)` satisfy `σ ≤ 2`.

**Non-vacuity, checked rather than assumed.**  The hypothesis `σ − β ≤ 2(σ−1)` forces
`β ≥ 2 − σ = 1 − (σ−1)`, and `σ − 1 < zeroFreeConst/log⁹N`, so the excluded range is
`1 − zeroFreeConst/log⁹N < β ≤ σ` — which reaches strictly left of `1`.  The theorem therefore
excludes zeros in a strip of width `≍ log^{-9}|γ|` to the left of the one-line, not merely in the
region `re ≥ 1` where nonvanishing was already known.

### The zero-free region, in region form

`riemannZeta_ne_zero_of_re_gt` — for `log N ≥ 3`, `|γ| ≥ 1`, `N ≥ 3 + 2|γ|`:

`1 − zeroFreeConst/(2 log⁹N) < β ≤ 1`  ⟹  `ζ(β + iγ) ≠ 0`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`; printed statement checked.

All six hypotheses of the previous form are discharged by the choice `σ = 1 + δ` with
`δ = zeroFreeConst/(2 log⁹N)`: `σ ≤ 2` and `β ≥ 0` from `δ ≤ 1/54`, `σ − β ≤ 2(σ−1)` from the
region hypothesis itself, `1 − 3/(4 log N) ≤ β` from `δ ≤ 3/(4 log N)` (which needs only
`log N ≤ log⁹N`), and `‖σ+2iγ‖ ≤ N` from `N ≥ 3 + 2|γ|`.

This is a genuine zero-free region for `ζ`, unconditional and formalized: a strip of width
`≍ log^{-9}|γ|` to the left of the one-line, at every height `|γ| ≥ 1` with `N` chosen as any
integer past `3 + 2|γ|` whose logarithm is at least `3`.

### The reciprocal bound

`norm_inv_riemannZeta_le` (`Sieve/ZeroFreeCombination.lean`) — for `σ > 1` and any `B₀` bounding
`‖ζ(σ+2it)‖`,

`‖1/ζ(σ+it)‖ ≤ exp(−(−22 − 3log(1+1/(σ−1)) − log B₀)/4)`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The lower bound for `‖ζ‖` inverts directly.  This is the shape a Perron-type argument for
`∑_{n ≤ x} μ(n)` consumes — the Dirichlet series of `μ` is `1/ζ`, so an explicit upper bound for
`‖1/ζ‖` on a contour is exactly what is needed to move the contour left of `re = 1`.

The prime number theorem for `μ` (`∑_{n≤x} μ(n) = o(x)`) is one of the classical inputs this card
lists, and mathlib does not have it.  This bound is the first ingredient; the Perron formula and the
contour estimate are not built, and that remains a substantial classical development rather than a
short step.

### The Möbius L-series, bounded

- `LSeries_moebius_eq_inv` — for `re s > 1`, `L(μ, s) = 1/ζ(s)`, from mathlib's
  `LSeries_one_mul_Lseries_moebius` and `LSeries_one_eq_riemannZeta` together with the nonvanishing.
- `norm_LSeries_moebius_le` — hence `‖L(μ, σ+it)‖ ≤ exp(−(−22 − 3log(1+1/(σ−1)) − log B₀)/4)`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is the object a Perron argument integrates: `∑_{n≤x} μ(n)` is recovered from `L(μ,s)·x^s/s`
along a vertical contour, and the bound above controls the integrand.  What is missing between here
and `∑_{n≤x} μ(n) = o(x)` is the Perron formula itself plus the contour shift — mathlib has neither,
and both are substantial.

Recording the position plainly: the card lists the prime number theorem as a classical input; the
corpus now has the zero-free region and the reciprocal bound that a proof of it would start from,
but not the proof.

### A uniform Möbius L-series bound, and the corpus's Perron formula

`norm_LSeries_moebius_le_uniform` — for `σ > 1` and every height `t`,

`‖L(μ, σ+it)‖ ≤ e^{11/2}·(1 + 1/(σ−1))`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.  The height-dependence disappears
because the trivial bound `‖ζ(σ+2it)‖ ≤ 1 + 1/(σ−1)` is itself uniform, so `B₀` can be taken
independent of `t`.

**The corpus already owns the Perron step.**  `HTGeometry/SmoothWeightPerron.tsum_mul_smoothWeight_eq_integral`
gives, for unit-bounded coefficients with `a₀ = 0` and `σ > 1`,

`2π·∑' a_n·smoothWeight N H n = ∫ L(a, σ+iy)·mellin(smoothWeight)(σ+iy) dy`,

and `μ` satisfies both hypotheses.  Combined with the uniform bound above, the smoothed Möbius sum
is at most `e^{11/2}(1 + 1/(σ−1))·∫‖mellin(smoothWeight)‖/(2π)`.

So the remaining gap to `∑_{n≤x} μ(n) = o(x)` is not the Perron formula — it is the size of
`∫‖mellin(smoothWeight)‖` against the length of the smoothed sum, and the removal of the smoothing.
That is a much narrower gap than "mathlib has no Perron formula", which is what I had recorded
before checking the corpus.

### The smoothed Möbius sum, bounded

`Sieve/MoebiusPerron.lean`:

- `tsum_cpow_neg_eq_LSeries` — the Perron formula's inner series `∑' aₙ n^{-s}` *is* `LSeries a s`,
  for `a₀ = 0` (the `n = 0` terms agree by both conventions).
- `norm_tsum_moebius_smoothWeight_le` — **the bound**: for `N, H > 0` and `σ > 1`,

  `‖2π·∑' μ(n)·w(n)‖ ≤ e^{11/2}(1 + 1/(σ−1))·∫‖mellin w(σ+iy)‖ dy`,

  where `w = smoothWeight N H`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This joins three separately-built layers: the corpus's smoothed Perron formula, mathlib's identity
`L(μ,s) = 1/ζ(s)`, and this session's zero-free machinery bounding `1/ζ` uniformly in the height.
`μ` satisfies the Perron hypotheses (`‖μ(n)‖ ≤ 1`, `μ(0) = 0`) directly.

What remains for `∑_{n≤x} μ(n) = o(x)` is quantitative: the size of `∫‖mellin(smoothWeight)‖`
relative to the mass of the cutoff, and the passage from the smoothed sum to the sharp one.  Both
concern `smoothWeight` alone — no further property of `ζ` or `μ` enters.

### Correction — the corpus also owns the contour shift

The note above said the passage from the smoothed bound to `∑_{n≤x} μ(n) = o(x)` was "quantitative,
concerning `smoothWeight` alone".  That understated what exists and misstated what is missing.
`HTGeometry/SmoothWeightShift.lean` owns the **Perron contour shift**:

`integral_mul_mellin_smoothWeight_shift` — if `F` is holomorphic on the vertical strip
`c ≤ re s ≤ d` with `c > 0` and satisfies `‖F s‖ ≤ K(2 + |im s|)^A` there, then the vertical
integral of `F · mellin(smoothWeight)` is the same on both edges.

Together with `SmoothWeightMellin` (convergence, integration by parts, decay) and
`tendsto_horizontal_mul_mellin_smoothWeight` (the horizontal edges vanish), the analytic
infrastructure for moving the contour is complete.

**What is actually missing** is the hypothesis `hFbd` for `F = 1/ζ`: a polynomial bound for `1/ζ` on
a strip reaching *left* of `re = 1`.  This session's `norm_inv_riemannZeta_le` gives that only for
`σ > 1`; inside the zero-free region it requires a quantitative lower bound for `‖ζ‖`, which is the
classical `ζ'/ζ` estimate and is not built.

So the chain is: Perron ✓ (corpus), `L(μ) = 1/ζ` ✓ (mathlib), uniform bound for `σ > 1` ✓ (this
session), contour shift ✓ (corpus), zero-free region ✓ (this session) — and the one gap is the
*quantitative* lower bound for `‖ζ‖` inside the region, not merely its nonvanishing.

### A structural mismatch, found by checking

Searching the corpus for an existing quantitative lower bound on `‖ζ‖` inside the critical strip
found none (`HighExponentShellZeroFree` is a different construction — shell indicators, not a `ζ`
lower bound).  But the more important finding is a mismatch between two pieces that at first look
composable:

`integral_mul_mellin_smoothWeight_shift` requires `F` holomorphic and polynomially bounded on a
**fixed** vertical strip `c ≤ re s ≤ d`, and its horizontal edges are killed at `±∞`, so the bound
must hold for *all* heights.  For `F = 1/ζ` that needs a zero-free region of **fixed width** to the
left of `1` — which classical methods do not give and should not be expected to give: the region
`1 − c/log⁹|t|` narrows as `|t|` grows, so on any fixed strip `1 − ε ≤ re s` there are heights where
`ζ` may vanish.

The classical proof avoids this by truncating the contour at height `T` and using a `T`-dependent
rectangle, the horizontal edges being controlled by the decay of the cutoff's transform rather than
sent to infinity.  The corpus's shift is the untruncated version.

So the honest gap on this line is now two items, not one:

1. a quantitative lower bound for `‖ζ‖` inside the zero-free region (the classical `ζ'/ζ` estimate);
2. a **truncated** contour shift, the corpus's being stated for a fixed strip over all heights.

Neither is open research; both are classical and substantial.  Recording them precisely is worth
more than a partial attempt at either.

### The truncated contour shift — gap 2 closed

`integral_vertical_sub_eq_horizontal` (`Sieve/TruncatedContourShift.lean`) — for `G` holomorphic on
the closed strip `c ≤ re s ≤ d`,

`i·∫_{−T}^{T} G(d+iy) dy − i·∫_{−T}^{T} G(c+iy) dy = ∫_c^d G(x+iT) dx − ∫_c^d G(x−iT) dx`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is Cauchy's theorem on the rectangle, kept in truncated form.  It was already inside the proof
of the corpus's untruncated `integral_vertical_line_eq_of_horizontal_tendsto` as an intermediate
`have`; exposing it as a theorem is what the `T`-dependent contour needs, since holomorphy is now
required only on the finite rectangle, not at every height.

That is the second of the two gaps recorded above.  The remaining one is the first: a quantitative
lower bound for `‖ζ‖` inside the zero-free region, giving the polynomial bound for `1/ζ` on the
truncated rectangle.

### The quantitative lower bound left of the abscissa — gap 1 closed

- `norm_riemannZeta_sub_le` (`Sieve/ZetaDerivBound.lean`) — the mean value inequality without a
  zero: `‖ζ(c) − ζ(z)‖ ≤ M‖c − z‖` along a segment avoiding the pole with `‖ζ'‖ ≤ M`.
- `le_norm_riemannZeta_left` (`Sieve/ZeroFreeAssembly.lean`) — **the bound**: if
  `M(σ−β) ≤ exp((−22 − 3log(1+1/(σ−1)) − log B₀)/4)/2` then

  `exp((−22 − 3log(1+1/(σ−1)) − log B₀)/4)/2 ≤ ‖ζ(β + iγ)‖`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

The mechanism is the same one that gives the zero-free region, used to keep half the lower bound
instead of merely denying a zero: the value at `σ > 1` is bounded below by three-four-one, and the
mean value inequality transports that bound left, losing at most `M(σ−β)`.

Both gaps identified above are now closed.  The line reads, end to end and unconditionally:
Perron ✓ (corpus) · `L(μ) = 1/ζ` ✓ (mathlib) · uniform bound for `σ > 1` ✓ · truncated contour shift
✓ · quantitative lower bound for `‖ζ‖` left of `1` ✓.  What remains is assembling them into
`∑_{n≤x} μ(n) = o(x)` — choosing the rectangle, applying the shift, and estimating the residue at
`s = 1` — with no missing ingredient.

### The reciprocal bound left of the abscissa

`norm_inv_riemannZeta_left_le` — under the hypotheses of the previous lemma,

`‖1/ζ(β + iγ)‖ ≤ 2 / exp((−22 − 3log(1+1/(σ−1)) − log B₀)/4)`.

Unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

This is the `hFbd` hypothesis that `integral_vertical_sub_eq_horizontal` needs for `F = 1/ζ`: an
explicit bound on the reciprocal at points left of `1`, in terms of the same parameters that control
everything else on this line.

Current state of the `μ`-summatory route, all unconditional and in the corpus:

| step | source |
|---|---|
| smoothed Perron formula | `HTGeometry/SmoothWeightPerron` |
| `L(μ,s) = 1/ζ(s)` | mathlib, packaged in `Sieve/MoebiusPerron` |
| `‖1/ζ‖` bound for `σ > 1` | `Sieve/ZeroFreeCombination` |
| truncated contour shift | `Sieve/TruncatedContourShift` |
| `‖ζ‖` lower bound left of `1` | `Sieve/ZeroFreeAssembly` |
| `‖1/ζ‖` bound left of `1` | `Sieve/ZeroFreeAssembly` |

The assembly into `∑_{n≤x} μ(n) = o(x)` is not done.

### An obstruction in the assembly — mathlib's junk value at `s = 1`

Attempting the assembly surfaces a formal obstruction worth recording before anyone repeats the
attempt.

The contour shift must cross `re = 1`, and the crossing includes the point `s = 1`.  Mathlib's
`riemannZeta` is the analytic continuation, which has a *pole* there; `riemannZeta 1` is a junk
value, nonzero by `riemannZeta_one_ne_zero`.  So the function `fun s => (riemannZeta s)⁻¹` takes a
nonzero junk value at `s = 1` while its limit there is `0` — it is **discontinuous at exactly the
point the contour crosses**, and `integral_vertical_sub_eq_horizontal` cannot be applied to it.

Mathematically there is no singularity: `1/ζ` has a removable singularity at `1` with value `0`,
since `ζ` has a simple pole.  The formal fix is to work with the corrected function and prove it
differentiable at `1`, for which mathlib supplies `riemannZeta_residue_one`
(`(s−1)ζ(s) → 1` as `s → 1`) and the pattern already used in `LSeries/Nonvanishing.lean`:
`Function.update (fun s ↦ (s − 1) * riemannZeta s) 1 1`.  Then
`1/ζ(s) = (s−1) · [1/((s−1)ζ(s))]`, a product of a polynomial and a function that is nonvanishing
and holomorphic near `1`.

So the assembly needs one more ingredient than the table above suggests: the removable-singularity
correction of `1/ζ` at `s = 1`.  Recording it rather than half-building it — the estimates on either
side are unaffected.

#### Resolved — `RHTower/Sieve/InvZetaRegular.lean`

The obstruction above is closed, and it cost less than expected because the corpus already owned the
entire unit `G(s) = (s-1)·ζ(s)` (`RHTower/ZetaLogDerivResidue.lean`: `zetaResidueUnit`,
`analyticAt_zetaResidueUnit`).  The removable-singularity correction of `1/ζ` needs no
`Function.update` and no case split at all:

`invZeta s = (s - 1) · G(s)⁻¹`.

Off the pole the outer `(s-1)` cancels the one inside `G` and this *is* `1/ζ(s)`
(`invZeta_eq_inv`); at `s = 1` it is `0 · 1 = 0` (`invZeta_one`), the value of the analytic
continuation.  So one formula covers both, and differentiability at `1` is immediate from
analyticity of `G` and `G(1) = 1 ≠ 0` (`differentiableAt_invZeta_one`).

Built in the same module:

| statement | content |
|---|---|
| `zetaResidueUnit_ne_zero_iff` | off the pole, `G` vanishes exactly where `ζ` does |
| `differentiableAt_invZeta_of_zeta_ne_zero` | holomorphy at a nonzero of `ζ` |
| `norm_invZeta_eq` | `‖invZeta s‖ = ‖1/ζ(s)‖` off the pole — every earlier bound transfers verbatim |
| `differentiableOn_invZeta_verticalStrip` | holomorphy on a zero-free strip |
| `integral_invZeta_vertical_sub_eq_horizontal` | the contour shift, strip hypothesis |
| `integral_vertical_sub_eq_horizontal_rect` | Cauchy on the rectangle, holomorphy assumed only there |
| `differentiableOn_invZeta_rect` | holomorphy on a zero-free rectangle |
| `integral_invZeta_vertical_sub_eq_horizontal_rect` | the contour shift, rectangle hypothesis |

All `[propext, Classical.choice, Quot.sound]`.

The rectangle forms matter, and the strip form is the one that would have been wasted work: the
zero-free region of `ζ` narrows with the height, so **no** strip `c ≤ re s ≤ d` with `c < 1` is
zero-free, and the strip-hypothesis shift is unusable for `1/ζ` however good the estimates are.  On
a rectangle `[c,d] × [-T,T]` the classical region does supply zero-freeness, with `c = 1 - c₀/log T`.
So the assembly's contour step is now stated in the only form that can consume the zero-free region.

What remains for `∑_{n≤x} μ(n) = o(x)`: choose `c(T)` from the region, bound the two horizontal edges
and the left vertical edge, and let `T → ∞`.  There is no missing ingredient of a different kind —
the residue at `s = 1` contributes nothing precisely because `invZeta 1 = 0`, which is the content
of `1/ζ` having a zero rather than a pole there, and is now a theorem rather than a remark.

#### The contour hypothesis is now discharged — `RHTower/Sieve/ZeroFreeRectangle.lean`

The rectangle shift above still *assumed* zero-freeness.  That hypothesis is now proved, so the
contour step is unconditional.

The quantitative region in `ZeroFreeAssembly` (`riemannZeta_ne_zero_of_re_gt`) covers heights
`|γ| ≥ 1` only, and near the real axis the argument is of a different kind.  There the point is that
`ζ` is nonvanishing on the whole closed segment `{1 + it : |t| ≤ T}`: off the pole because
`re s = 1`, and *at* `s = 1` because `ζ` has a pole there, so the entire unit `G = (s-1)ζ` takes the
value `1`.  The pole, which was the obstruction two sections ago, is what supplies the nonvanishing
at the one point the line argument cannot reach.

That segment is compact and `{G ≠ 0}` is open, so `IsCompact.exists_thickening_subset_open` gives a
whole thickening of it inside the nonvanishing locus — no sequence extraction, no Lebesgue number.

| statement | content |
|---|---|
| `zetaResidueUnit_ne_zero_on_one_line` | `G ≠ 0` on the entire abscissa `re s = 1`, pole included |
| `continuous_zetaResidueUnit` | `G` is continuous, being entire |
| `exists_zero_free_box` | for every `T`, some `δ > 0` with no zeros in `1-δ ≤ re s ≤ 1`, `\|im s\| ≤ T` |
| `exists_zero_free_rect` | the box glued to `re s ≥ 1`: a zero-free rectangle `[c,d] × [-T,T]`, `1-δ ≤ c ≤ 1 ≤ d` |
| `exists_differentiableOn_invZeta_rect` | `invZeta` is holomorphic there |
| `exists_integral_invZeta_shift` | the shift identity itself, hypothesis-free apart from `0 ≤ T` |

All `[propext, Classical.choice, Quot.sound]`.

`exists_integral_invZeta_shift` is the honest statement of the contour step: *at every height the
contour may be pushed to the left of the abscissa, and the crossing costs nothing.*  Nothing about
zeros of `ζ` is assumed anywhere in it.

Note what this `δ` is and is not.  It is genuine and unconditional, but it is obtained from
compactness and therefore carries no rate in `T` — which is exactly right for the low box, where the
quantitative region says nothing, and useless for large `T`, where `riemannZeta_ne_zero_of_re_gt`
supplies `δ ≍ log^{-9}T` instead.  The remaining work for `∑_{n≤x} μ(n) = o(x)` is the estimate, not
the geometry: bound the left vertical edge and the two horizontal edges of this rectangle, with
`c = c(T)` taken from the quantitative region, and let `T → ∞`.

#### The horizontal edges — `RHTower/Sieve/HorizontalEdgeBound.lean`

In the untruncated shift (`HTGeometry/SmoothWeightShift`) the horizontal edges vanish in the limit
and never appear as terms.  That shift is unusable for `1/ζ` — it demands holomorphy on a *full*
strip `c ≤ re s ≤ d` with `c < 1`, which is a quasi-RH statement, not something to be proved.  So
the contour must be truncated and the edges become explicit terms.

They cost almost nothing, and the reason is worth stating: the estimate is carried entirely by the
cutoff, not by `1/ζ`.  `exists_bound_mellin_smoothWeight` bounds
`‖s‖ · ∏_{i<j} ‖s+1+i‖ · ‖W(s)‖` uniformly on `0 < re s ≤ σmax`, and every one of those `j+1`
factors dominates `|im s|` — because the shifts `1 + i` are *real*, so they leave the imaginary part
untouched.  Hence `W` decays in the height faster than any fixed power, uniformly in the abscissa.

| statement | content |
|---|---|
| `exists_bound_mellin_smoothWeight_im_pow` | `\|im s\|^{j+1}·‖W(s)‖ ≤ C` on `0 < re s ≤ σmax`, every `j` |
| `norm_mellin_smoothWeight_le_div` | the same in divided form, `‖W(s)‖ ≤ C/\|im s\|^{j+1}` |
| `exists_horizontal_edge_bound` | a horizontal edge contributes `≤ M·C·T^{-(j+1)}·(d-c)` |

All `[propext, Classical.choice, Quot.sound]`.

The order `j` is arbitrary, so the two horizontal edges may be made to decay faster than any fixed
power of the truncation height, with the constant depending only on the cutoff and on `σmax` — not
on `c`, and not on the zero-free region.  The only input from the other factor is a bound `M` on the
segment itself.

So of the four edges of the truncated rectangle, the right one is the Perron integral, the two
horizontal ones are now controlled, and what is left is the left vertical edge — where the estimate
must genuinely use the zero-free region, via `norm_inv_riemannZeta_left_le`.

#### The left vertical edge — `RHTower/Sieve/VerticalEdgeBound.lean`

The left edge is where the saving lives and where the zero-free region is genuinely spent.  The
cutoff's transform is at most `(N+H)^c / c` on the line `re s = c`, so pushing `c` below `1`
replaces the trivial size `N` by `N^c`; what is paid for it is a bound on the other factor along
that edge.

| statement | content |
|---|---|
| `norm_mellin_smoothWeight_line_tail` | order-two decay on a line: `‖W(c+iy)‖ ≤ C·y^{-2}` for `\|y\| ≥ 1` |
| `exists_bound_integral_norm_mellin_line` | `∫_{-T}^{T} ‖W(c+iy)‖ dy ≤ 2(N+H)^c/c + 2C` |
| `exists_vertical_edge_bound` | the edge itself: `≤ M·(2(N+H)^c/c + 2C)` |

All `[propext, Classical.choice, Quot.sound]`.

The content of the middle statement is that the bound **does not grow with `T`** — the vertical mass
of `W` is finite, split as the trivial bound on `|y| ≤ 1` and the convergent order-two tail beyond.
So truncating higher never costs anything on this edge, and the left edge is `sup‖F‖` times a
constant rather than times `T`.  Together with the horizontal edges decaying like `T^{-(j+1)}` for
every `j`, the whole truncated contour is now *height-stable*: no edge grows with the truncation.

That was the one structural risk in the truncated route — that the price of truncating (edges that
the untruncated shift never has to name) would grow with `T` and cancel the saving from `c < 1`.  It
does not.

All four edges are now accounted for:

| edge | source | size |
|---|---|---|
| right vertical (`re s = d > 1`) | `HTGeometry/SmoothWeightPerron` | the Perron integral itself |
| top and bottom horizontal | `Sieve/HorizontalEdgeBound` | `M·C·T^{-(j+1)}·(d-c)`, any `j` |
| left vertical (`re s = c < 1`) | `Sieve/VerticalEdgeBound` | `M·(2(N+H)^c/c + 2C)`, no `T` |
| Cauchy identity relating them | `Sieve/ZeroFreeRectangle` | unconditional at every height |

What remains is exactly one estimate: the bound `M` for `‖invZeta‖` on the left edge and the
horizontal edges, as a function of `T`, from `norm_inv_riemannZeta_left_le` and the zero-free
region.  Everything the estimate has to be fed into is built.

#### Truncating the Perron line — `RHTower/Sieve/TruncationError.lean`

One step was still implicit in the edge table: the smoothed Perron formula is an exact identity on
the **whole** line `re s = d`, with no truncation error of its own, whereas the rectangle shift
consumes a *truncated* vertical integral.  The passage between them is a real cost and had not been
bounded.

| statement | content |
|---|---|
| `integral_tail_norm_mellin_le` | `∫_T^R ‖W(c+iy)‖ dy ≤ C/T`, uniformly in `R` |
| `integral_tail_norm_mellin_le'` | the same for `∫_{-R}^{-T}` |
| `exists_bound_truncation_error` | `‖∫_ℝ F·W − ∫_{-T}^{T} F·W‖ ≤ 2MC/T` |

All `[propext, Classical.choice, Quot.sound]`.

The proof bounds the two tails uniformly in the outer height `R` and then passes to the limit
through `intervalIntegral_tendsto_integral`, so no improper-integral machinery is needed and the
whole argument stays in interval integrals.  As with the other edges the hypotheses on the second
factor are only a bound `M` on the line and continuity — nothing about `ζ`.

So the chain from the Perron identity to the shifted contour is complete:

    2π ∑ μ(n)w(n)  =  ∫_ℝ (1/ζ)(d+iy) W(d+iy) dy          exact, HTGeometry/SmoothWeightPerron
                   =  ∫_{-T}^{T} … dy      + O(M_d C/T)     Sieve/TruncationError
                   =  ∫_{-T}^{T} (1/ζ)(c+iy) W(c+iy) dy
                        + horizontal edges                  Sieve/ZeroFreeRectangle (Cauchy)
                                                            Sieve/HorizontalEdgeBound
                   =  O(M_c · ((N+H)^c/c + C))              Sieve/VerticalEdgeBound

with every step unconditional and every constant depending only on the cutoff.  The single
remaining input is `M_c`, the bound for `‖invZeta‖` on the left edge as a function of `T`, which is
where the zero-free region is spent and which `norm_inv_riemannZeta_left_le` was built to produce.

#### The left-edge bound splits at height one — `RHTower/Sieve/InvZetaLowBox.lean`

The remaining input `M_c` does **not** come from `norm_inv_riemannZeta_left_le` alone, and it is
worth recording why, because the reason is structural rather than a matter of sharpening.

That theorem bounds `‖1/ζ(β+iγ)‖` by moving left from `σ > 1` along the horizontal segment at height
`γ`, and it needs that segment to avoid the pole.  At `γ = 0` the segment runs along the real axis
straight through `s = 1`, so the hypothesis `hne` is false there and the theorem says nothing.  The
left edge of the truncated rectangle passes through that height.  So the left-edge bound splits at
`|γ| = 1` exactly as the zero-freeness did — and for the same reason, the pole.

Near the axis the bound comes from compactness, as it did for `exists_zero_free_box`:

| statement | content |
|---|---|
| `isCompact_reProdIm_Icc` | a closed complex box is compact |
| `exists_bound_invZeta_low_box` | `‖invZeta‖ ≤ M` on `1-δ ≤ re s ≤ d`, `\|im s\| ≤ 1` |
| `exists_bound_invZeta_line_low` | the same along the part of a vertical line with `\|y\| ≤ 1` |

All `[propext, Classical.choice, Quot.sound]`.

The pole is again what makes this work rather than what obstructs it: `invZeta` is *continuous* on
the box only because `invZeta 1 = 0` is the analytic value, and a continuous function on a compact
set is bounded.  The constant carries no rate, which is correct here — it is independent of the
truncation height, so it never competes with the `T`-dependence.

What is left is a single estimate with a single free parameter: the bound for `‖invZeta(c+iy)‖` for
`1 ≤ |y| ≤ T`, from `norm_inv_riemannZeta_left_le` with `σ = 1 + δ`, the derivative bound from
`norm_deriv_riemannZeta_le_log_of_re_ge`, and `δ ≍ log^{-9}T` from the zero-free region.

#### The high half of the left-edge bound — `RHTower/Sieve/InvZetaSegmentBound.lean`

The other half of the split, `1 ≤ |γ|`, where the estimate is quantitative.  Two of the three
hypotheses of `norm_inv_riemannZeta_left_le` are now discharged unconditionally.

| statement | content |
|---|---|
| `segment_ne_one_of_im_ne_zero` | the segment misses the pole at any nonzero height |
| `norm_deriv_riemannZeta_segment_le` | Cauchy's estimate at *every* point of the segment at once |
| `norm_inv_riemannZeta_left_le_segment` | the reciprocal bound with the geometry discharged |
| `norm_invZeta_left_le_segment` | the same for `invZeta`, which is what the contour uses |

All `[propext, Classical.choice, Quot.sound]`.

The first is cheap for a reason worth naming: every point of the horizontal segment has imaginary
part exactly `γ`, and the pole sits at height `0`, so at nonzero height the segment misses it for
purely geometric reasons — no estimate involved.  The second reduces to a single inequality
`σ + |γ| + R ≤ N` covering the whole segment, because the segment stays inside the strip
`β ≤ re s ≤ σ` and `Complex.norm_le_abs_re_add_abs_im` then bounds every point uniformly.

What remains is exactly one hypothesis, `hhalf`:

    (2 + e·log N + e/(|γ|-R) + 2e)/R · (σ - β)  ≤  exp((-22 - 3log(1+1/(σ-1)) - log B₀)/4) / 2

This is the balance, and the balance is real rather than a matter of bookkeeping.  Writing
`σ - 1 = δ`, `B₀ ≍ log T` (from `norm_riemannZeta_le_log_uniform`, *not* `1 + 1/δ`), `R ≍ 1/log N`
and `M ≍ log²N`, the two sides read

    log²N · (σ - β)      vs      δ^{3/4} · (log T)^{-1/4}

so with `δ = A·log^{-9}T` and `σ - β ≍ log^{-9}T` both sides are of order `log^{-7}T`, and the
inequality reduces to a numerical comparison in `A` alone.  That the exponents match at `9` is not
an accident: it is the same balance that produces the corpus's zero-free region
`riemannZeta_ne_zero_zero_free`, and the reason both land on `log^9`.

Using `B₀ ≍ log T` rather than `1 + 1/δ` is essential and easy to get wrong — with the cruder `B₀`
the lower bound degrades to order `δ` and the comparison fails at every exponent, since `M` grows
while the right side would not.

#### The balance, discharged — `RHTower/Sieve/HalfComparison.lean`

The `hhalf` hypothesis is now a theorem, and the balance turned out to need **no new numerical
constant** — which is the useful discovery here, since a fresh constant would have had to be
optimised against the zero-free region's own.

| statement | content |
|---|---|
| `quarter_comparison_scaled` | `quarter_comparison` applied at `δ·κ⁴` instead of `δ` |
| `half_comparison` | `32L²·D ≤ (lower bound at σ)/2` whenever `D⁴L⁹ < c·δ³` |

Both `[propext, Classical.choice, Quot.sound]`.

The mechanism: write the distance moved left as `σ - β = κ·(σ - 1)`.  The lower bound scales like
the `3/4` power of the offset, so the two sides of the comparison differ by exactly
`κ·(σ-1)^{1/4}` — which is `(δκ⁴)^{1/4}`.  So the comparison at distance `κδ` *is* the zero-free
comparison at offset `δκ⁴`, and `quarter_comparison` settles it verbatim with `c = zeroFreeConst`,
the constant already in the corpus.

Concretely the admissible choice is `σ = 1 + δ` with `δ ≍ c/L⁹` and `1 - β ≍ δ/8`, since
`D = σ - β = 9δ/8` gives `D⁴/δ³ = (9/8)⁴δ ≈ 1.60δ`, comfortably below `c/L⁹` when `δ ≤ c/(2L⁹)`.
So the left edge may be placed at

    c(T) = 1 - zeroFreeConst / (16 · log⁹ N),      N ≍ 3 + 2T

which is the same order as the zero-free region itself — the estimate loses nothing relative to the
region it is built on.

Every hypothesis of `norm_invZeta_left_le_segment` is now discharged except the purely arithmetic
ones in `N`, `σ`, `β`, `|γ|`.  The bound for `‖invZeta‖` on the left edge is therefore complete in
both halves: `|γ| ≤ 1` by compactness (`InvZetaLowBox`), `|γ| ≥ 1` by this estimate.

#### The left edge bound, assembled — `RHTower/Sieve/InvZetaLeftEdge.lean`

`norm_invZeta_left_le_explicit` — unconditional, `[propext, Classical.choice, Quot.sound]`:

for every height `|γ| ≥ 1` and every `N` with `log N ≥ 3` and `N ≥ 3 + 2|γ|`,

    ‖invZeta( (1 - c/(16 log⁹N)) + iγ )‖
        ≤ 2 / exp( (-22 - 3·log(1 + 2log⁹N/c) - log(5/2 + log N)) / 4 )

with `c = zeroFreeConst`.  Every hypothesis is arithmetic in `N` and `|γ|`; nothing about the zeros
of `ζ` is assumed, and nothing is left open.

The right-hand side is of size `log^{27/4}N · log^{1/4}N = log^7 N` — polynomial in `log N`, which is
what the contour argument needs and all that it needs.  The abscissa is `1 - c/(16 log⁹N)`: the same
constant and the same exponent as the zero-free region, so the estimate loses nothing relative to
the region it stands on.  The factor `16` rather than `2` is exactly the room the comparison
`D⁴log⁹N < c·δ³` demands, no more.

With this the left-edge input is complete on both halves of the split:

| range | source | shape |
|---|---|---|
| `\|γ\| ≤ 1` | `Sieve/InvZetaLowBox` | a constant, no rate, no `T`-dependence |
| `\|γ\| ≥ 1` | `Sieve/InvZetaLeftEdge` | explicit, `≍ log⁷N` |

and every ingredient listed in the four-edge table now exists as an unconditional theorem.

#### The whole left edge in one bound — `RHTower/Sieve/InvZetaLeftLine.lean`

The two halves are proved at different heights and by different means, so merging them is not
automatic: the line `re s = 1 - c/(16 log⁹N)` must lie inside the compact box that supplies the
low-height constant.  It does as soon as `log⁹N ≥ c/(16δ₀)`, and since `log N → ∞` that is eventually
free.

| statement | content |
|---|---|
| `norm_invZeta_left_line_le` | one bound on the whole edge, given the compatibility condition |
| `exists_bound_invZeta_left_line` | the condition eliminated: `∃ N₀ M₀`, valid for all `N ≥ N₀` |

Both `[propext, Classical.choice, Quot.sound]`.

The merged bound is

    ‖invZeta( (1 - c/(16 log⁹N)) + iy )‖  ≤  max M₀ ( 2 / exp((-22 - 3log(1 + 2log⁹N/c)
                                                       - log(5/2 + log N))/4) )

for every `y` with `3 + 2|y| ≤ N` — i.e. on the entire left edge of the rectangle truncated at
height `T = (N-3)/2`.  `M₀` is an absolute constant; the second argument of the `max` is `≍ log⁷N`.

This completes every input to the contour argument.  Collecting the modules built for this route:

| ingredient | module |
|---|---|
| removable-singularity correction of `1/ζ` | `InvZetaRegular` |
| zero-free rectangle at every height | `ZeroFreeRectangle` |
| horizontal edges | `HorizontalEdgeBound` |
| left vertical edge (mass of the cutoff) | `VerticalEdgeBound` |
| truncating the Perron line | `TruncationError` |
| `‖1/ζ‖` near the real axis | `InvZetaLowBox` |
| `‖1/ζ‖` along the segment | `InvZetaSegmentBound` |
| the balance | `HalfComparison` |
| `‖1/ζ‖` on the left line, explicit | `InvZetaLeftEdge` |
| the whole left edge, one bound | `InvZetaLeftLine` |

Every one is unconditional and axiom-clean.  What remains for `∑_{n≤x} μ(n) = o(x)` is no longer an
estimate but a choice: tie `N` to `x` (equivalently `T` to `x`) so that `x^{-c/(16log⁹N)}` beats the
`log⁷N` factor, and combine the five already-proved inequalities.  The natural choice is
`log N ≍ (log x)^{1/10}`, giving a saving of `exp(-κ(log x)^{1/10})`.

#### Shifting the Perron integrand — `RHTower/Sieve/InvZetaProductShift.lean`

A correction to the edge table: the shift proved in `ZeroFreeRectangle` is for `invZeta` *alone*,
but the object the Perron formula integrates is the **product** `invZeta · W`, and Cauchy's theorem
applies to what is actually integrated.  The `invZeta`-only identity is not directly usable.

The gap is small — `W` is holomorphic on every strip inside `Re s > 0`, so the product inherits
holomorphy on a zero-free rectangle — but it is a real step, and the four-edge identity has to be
restated for the product.

| statement | content |
|---|---|
| `tsum_moebius_cpow_eq_invZeta` | on `Re s > 1` the Möbius Dirichlet series *is* `invZeta s` |
| `continuous_invZeta_line` | continuity of `invZeta` along a line right of the abscissa |
| `differentiableOn_invZetaW_rect` | holomorphy of the product on a zero-free rectangle |
| `integral_invZetaW_vertical_sub_eq_horizontal_rect` | the four-edge identity for the product |
| `exists_integral_invZetaW_shift` | the same with the zero-free hypothesis discharged |

All `[propext, Classical.choice, Quot.sound]`.

`tsum_moebius_cpow_eq_invZeta` is the hinge of the whole route: the Perron formula produces
`∑' μ(n)·n^{-s}` and every analytic estimate built above is stated for `invZeta`.  Without the
identification the two halves never meet, and the identification needs `s ≠ 1` — which on
`Re s > 1` is free, but is the reason the Perron abscissa must be taken strictly right of `1` rather
than at it.

The contour identity is now in the exact shape the assembly consumes.

#### The four edges combined — `RHTower/Sieve/PerronEdgeAssembly.lean`

| statement | content |
|---|---|
| `norm_le_of_contour_edges` | Cauchy identity + four edge bounds ⟹ `‖P‖ ≤ E₁+E₂+E₃+E₄` |
| `tsum_moebius_smoothWeight_eq_invZeta_integral` | the Perron identity, restated for `invZeta` |
| `norm_tsum_moebius_smoothWeight_le_edges` | the smoothed Möbius sum bounded by the four edges |

All `[propext, Classical.choice, Quot.sound]`.

`norm_tsum_moebius_smoothWeight_le_edges` is the shape the route was aiming at:

    ‖ 2π · ∑ₙ μ(n)·w(n) ‖  ≤  E₁ + E₂ + E₃ + E₄

with `E₁` the truncation error, `E₂`, `E₃` the horizontal edges, `E₄` the left vertical edge, and
the only structural hypothesis being that `ζ` has no zeros in the rectangle — which
`exists_zero_free_rect` supplies unconditionally.

The combination itself is triangle inequality, and isolating it matters for a practical reason: the
four estimates were proved in four different modules with four different shapes, and this is the
one place where they have to agree on notation.  The factor `I` carried by the shift costs nothing
(`‖I • z‖ = ‖z‖`), which is why the identity could be left in its natural Cauchy form throughout.

The remaining step is arithmetic on this inequality: substitute the four proved estimates, tie
`N`, `T` and `d` together, and check that `E₁ + E₂ + E₃ + E₄ = o(N)`.  There is no analytic
ingredient left to construct.

#### The four estimates substituted — `RHTower/Sieve/PerronEdgeSubstitution.lean`

`exists_norm_tsum_moebius_smoothWeight_le` — unconditional, `[propext, Classical.choice, Quot.sound]`:

    ‖ 2π · ∑ₙ μ(n)·w(n) ‖  ≤  2·Md·C/T  +  2·Mh·C·(d-c)/T^{j+1}  +  Mc·(2(N+H)^c/c + 2C)

for every rectangle `0 < c ≤ d ≤ σmax`, `1 < d`, `T ≥ 1` free of zeros of `ζ`, where `Md`, `Mh`,
`Mc` bound `invZeta` on the right line, the horizontal edges and the left line, and `C` depends only
on the cutoff, on `σmax` and on the decay order `j`.

Two of the earlier modules had to be generalised to make the substitution go through, and both
restrictions were artefacts of how the lemmas were first stated rather than of the mathematics:

- `exists_horizontal_edge_bound` assumed `0 < T`, so it could not be applied to the **bottom** edge
  at height `-T`.  Restated with `T ≠ 0` and `|T|^{j+1}`, it covers both.  It also fixed the upper
  abscissa as the parameter of the existential, which prevented `d` from varying under a single
  constant; it now takes `σmax` and quantifies `d ≤ σmax`.
- `exists_vertical_edge_bound` assumed the second factor continuous on the **whole** line.  That is
  false for `invZeta` on a line left of `1`: beyond the truncation height there may be zeros of `ζ`,
  and `invZeta` is genuinely discontinuous there.  The hypothesis is now `ContinuousOn` on
  `[-T, T]`, which is all the proof used and all that the zero-free rectangle supplies.

The second is worth recording as a trap: a global continuity hypothesis on `1/ζ` left of the
abscissa is not a harmless convenience — it is unprovable, and would have made the whole chain
vacuous.

What remains is the choice of `c, d, T` as functions of `N`, and the observation that the right-hand
side is then `o(N)`.

#### The three edge bounds supplied — `RHTower/Sieve/InvZetaEdgeBounds.lean`

The substitution theorem needs three bounds `Md`, `Mh`, `Mc` and a continuity hypothesis.  All four
are now theorems, and one choice makes the work collapse: **take the right abscissa to be exactly
`σ = 1 + c/(2 log⁹N)`**, the abscissa the zero-free comparison already uses.

With that choice the entire segment from the left line `1 - c/(16 log⁹N)` to `σ` lies inside the
range covered by the estimate, so the horizontal edges need no case split on the abscissa and no new
argument — they are the same expression as the left-edge bound.  Any other choice of `d` would have
forced a separate treatment of the part of the segment with `re s > σ`.

To make this available the left-edge estimate was generalised: `norm_invZeta_left_le_explicit` was
stated at the single abscissa `1 - c/(16 log⁹N)`, and is now the instance of
`norm_invZeta_left_le_range`, valid for every `β` in `[1 - c/(16 log⁹N), 1 + c/(2 log⁹N)]`.  The
generalisation is free: the comparison hypothesis only ever needed `σ - β ≤ D`, not equality.

| statement | content |
|---|---|
| `norm_invZeta_left_le_range` | the estimate on the whole abscissa range, not one line |
| `norm_invZeta_right_le` | `‖invZeta(d+iy)‖ ≤ e^{22/4}(1 + 1/(d-1))` on `Re s = d > 1` |
| `norm_invZeta_horizontal_le` | the horizontal edges, an instance of the range estimate |
| `continuousOn_invZeta_left_line` | continuity along the truncated left line |

All `[propext, Classical.choice, Quot.sound]`.

Every hypothesis of `exists_norm_tsum_moebius_smoothWeight_le` is now available at the concrete
rectangle

    c = 1 - c₀/(16 log⁹N),   d = 1 + c₀/(2 log⁹N),   T = (N-3)/2.

#### The concrete rectangle is zero-free — `RHTower/Sieve/ZeroFreeConcreteRect.lean`

`zero_free_concrete_rect` — unconditional, `[propext, Classical.choice, Quot.sound]`: the rectangle

    [ 1 - c₀/(16 log⁹N) ,  1 + c₀/(2 log⁹N) ] × [ -T , T ],     3 + 2T ≤ N

contains no zero of `ζ`, given `log N ≥ 3` and the single compatibility condition
`c₀/(16 log⁹N) ≤ δ₀` with `δ₀` the compactness constant of the low box.

An earlier statement of mine needs correcting.  I described `exists_zero_free_rect` as supplying the
zero-free hypothesis for the assembly.  It does not, and cannot: the `δ` it produces comes from
thickening a segment of half-length `T`, so it shrinks with the truncation height in an
*uncontrolled* way and can never be compared with `c₀/(16 log⁹N)`.  It is the right tool for
"a rectangle exists at every height", which is what it was built for, and the wrong tool for
"this rectangle is zero-free".

The correct input is the quantitative region, with the same split at height `1` as everywhere else
in this route: `riemannZeta_ne_zero_of_re_gt` above, the compactness box below, and
`riemannZeta_ne_zero_of_one_le_re` to the right of the abscissa.  Only the box's `δ₀` is
non-quantitative, and it is compared with `c₀/(16 log⁹N)` exactly once — a condition on `N` alone,
independent of `T`.

That the comparison is `T`-free is what makes the truncation height a free parameter, which the
final choice `T = (N-3)/2` then uses.

#### The contour bound at the concrete rectangle — `RHTower/Sieve/MoebiusContourBound.lean`

`exists_norm_tsum_moebius_smoothWeight_le_concrete` — unconditional,
`[propext, Classical.choice, Quot.sound]`.  With

    c(K) = 1 - c₀/(16 log⁹K),   d(K) = 1 + c₀/(2 log⁹K),   T(K) = (K-3)/2

(defined as `leftAbscissa`, `rightAbscissa`, `truncHeight`), and the edge bounds
`invZetaRightBound K ≍ log⁹K`, `invZetaEdgeBound K ≍ log⁷K`, there are `C, M₀ ≥ 0` and `K₀` such
that for all `K ≥ K₀`

    ‖ 2π ∑ₙ μ(n)·w(n) ‖ ≤ 2·R(K)·C/T(K)
                          + 2·E(K)·C·(d(K)-c(K))/T(K)^{j+1}
                          + max(M₀, E(K))·( 2(N+H)^{c(K)}/c(K) + 2C )

for every `j`, with `C` depending on the cutoff and on `j` but not on `K`.

`T(K) = (K-3)/2` is chosen so that `3 + 2T(K) = K` exactly — the largest height the quantitative
zero-free region supports at parameter `K`, and the reason the truncation height needs no separate
parameter.

The shape is now the classical one and each term is visibly what it should be:

| term | size | beaten by |
|---|---|---|
| truncation | `log⁹K / K` | any `K → ∞` |
| horizontal | `log⁷K · K^{-(j+1)}` | any `j ≥ 0` |
| left edge | `log⁷K · (N+H)^{1 - c₀/(16log⁹K)}` | the saving `exp(-c₀ log(N+H)/(16 log⁹K))` |

The last term is the whole content: it is `(N+H)` times `log⁷K·exp(-c₀ log(N+H)/(16 log⁹K))`, so
tying `K` to the cutoff by `log K ≍ (log N)^{1/10}` makes it `N·exp(-κ(log N)^{1/10})`, and the first
two terms are then negligible.  Choosing `K` is the only step left.

#### The saving made explicit — `RHTower/Sieve/MoebiusSaving.lean`

| statement | content |
|---|---|
| `rpow_leftAbscissa` | `x^{c(K)} = x · exp(-c₀·log x / (16 log⁹K))` |
| `exists_norm_tsum_moebius_smoothWeight_le_saving` | the contour bound with that substitution made |

Both `[propext, Classical.choice, Quot.sound]`.

The left-edge term is now literally

    max(M₀, E(K)) · ( 4·(N+H)·exp( -c₀·log(N+H) / (16 log⁹K) ) + 2C ),

the trivial size `N+H` multiplied by a decay that is positive as soon as `log(N+H)/log⁹K → ∞`.
`c(K) ≥ 1/2` handles the division by the abscissa with a factor `4`, which costs nothing.

This is the form in which the choice of `K` becomes an elementary optimisation rather than an
analytic step: two competing factors, `E(K) ≍ log⁷K` growing and `exp(-c₀ log(N+H)/(16 log⁹K))`
decaying, with `log K ≍ (log(N+H))^{1/10}` balancing them at `exp(-κ(log(N+H))^{1/10})`.  Nothing
about `ζ` enters any more — the remaining work is real-variable calculus on two explicit functions
of `K`.

#### Closed form of the edge bounds — `RHTower/Sieve/EdgeBoundForm.lean`

The two edge bounds were produced as reciprocals of exponentials of logarithms, a shape in which
their growth cannot be read.  Both collapse to products of powers — and these are *equalities*, not
estimates:

    invZetaRightBound K = e^{22/4}·(1 + 2log⁹K/c₀)
    invZetaEdgeBound  K = 2e^{22/4}·(1 + 2log⁹K/c₀)^{3/4}·(5/2 + log K)^{1/4}

| statement | content |
|---|---|
| `one_add_inv_offset` | `1 + 1/δ = 1 + 2log⁹K/c₀` |
| `invZetaRightBound_eq`, `invZetaEdgeBound_eq` | the closed forms |
| `invZetaEdgeBound_le_poly` | a polynomial majorant, `≤ 2e^{22/4}(1+2log⁹K/c₀)(5/2+log K)` |

All `[propext, Classical.choice, Quot.sound]`.

So the right-edge bound is exactly of order `log⁹K` and the edge bound of order
`log^{27/4}K · log^{1/4}K = log⁷K`, confirming the orders asserted earlier from the shape of the
three-four-one exponents.

The majorant deliberately throws away the fractional powers, replacing `log⁷K` by `log^{10}K`.  That
is wasteful and completely harmless: the competing factor `exp(-c₀ log x/(16 log⁹K))` decays faster
than any power of `log K` once `K` is tied to `x`, so no power of `log K` in the majorant can affect
the outcome.  Keeping the sharp exponent would only complicate the optimisation.

#### The contour parameter chosen — `RHTower/Sieve/ContourParameterChoice.lean`

    contourParam x = ⌈ exp( (log x)^{1/10} ) ⌉₊

| statement | content |
|---|---|
| `le_log_contourParam` | `(log x)^{1/10} ≤ log(contourParam x)` — no hypothesis needed |
| `log_contourParam_le` | `log(contourParam x) ≤ (log x)^{1/10} + 1` |
| `rpow_tenth_pow` | `((log x)^{1/10})^{10} = log x` |
| `le_saving_exponent` | `c₀(log x)^{1/10}/8192 ≤ c₀ log x / (16 log⁹(contourParam x))` |

All `[propext, Classical.choice, Quot.sound]`.

The last is the point of the choice: the saving in the contour bound is at least

    exp( -c₀ (log x)^{1/10} / 8192 ),

sub-polynomial in `x` but beating every power of `log x`, hence every power of
`log(contourParam x)` — which is what the edge bound contributes.  The constant `8192 = 16·512`
comes from `log K ≤ 2(log x)^{1/10}`, i.e. from the ceiling costing at most `+1`, raised to the
ninth power.

The exponent `1/10` is forced by the `log⁹` of the zero-free region: with `log K ≍ (log x)^θ` the
saving is `(log x)^{1-9θ}`, positive exactly when `θ < 1/9`, and `θ = 1/10` is the convenient
choice inside that range.  Nothing sharper is available from a `log⁹` region, and nothing weaker is
needed.

#### A defect in the vertical-edge estimate, and its repair — `RHTower/Sieve/VerticalMassSharp.lean`

Working out the size of the assembled bound exposes a real defect in `VerticalEdgeBound`, not a
looseness.  It is worth stating exactly, because the statement type-checks and looks harmless.

`exists_bound_integral_norm_mellin_line` bounds the vertical mass on the line `Re s = c` with a
decay constant valid on the *whole* range `0 < Re s ≤ σmax`.  That constant is
`≍ (N+H)^{σmax+j}/H^{j+1}·N` — it grows like `(N+H)^{σmax}` — while the mass on the line is of size
`(N+H)^c`.  In the application `c < 1 < σmax` and

    σmax - c ≈ c₀/(2log⁹K) + c₀/(16log⁹K) = (9/16)·c₀/log⁹K,

so the loss is a factor `exp( (9c₀/16)·log(N+H) / log⁹K )`.  The saving the contour is bought with
is `exp( -c₀·log(N+H) / (16 log⁹K) )`.  The loss is **nine times** the saving's exponent, so the
product diverges: the assembled bound with a global `σmax` is worse than trivial, and no choice of
`K` repairs it.

The repair is to take the decay constant on the line itself.  Nothing else in the proof changes:

| statement | content |
|---|---|
| `integral_norm_mellin_line_le` | `∫_{-T}^{T}‖W(c+iy)‖dy ≤ 2(N+H)^c/c + 2C`, `C` a bound at abscissa `c` |
| `norm_integral_vertical_edge_le` | the left edge with the same constant |

Both `[propext, Classical.choice, Quot.sound]`.  Both terms are now of size `(N+H)^c`, so the whole
left edge carries the saving.

The general lesson, worth carrying to the other edges: a constant quantified uniformly over an
abscissa *range* is not interchangeable with one taken at a point when the range straddles `1`,
because the cutoff's transform is exponential in the abscissa.  The horizontal edges and the
truncation error need the same audit — they are multiplied by `T^{-(j+1)}` and `T^{-1}`, which is
why the loss does not obviously sink them, but the sizes have to be checked rather than assumed.

#### The audit completed for the other two edges — `RHTower/Sieve/EdgeBoundsSharp.lean`

| statement | content |
|---|---|
| `norm_horizontal_edge_le` | a horizontal edge, decay constant supplied as a hypothesis |
| `norm_truncation_error_le` | the truncation error, likewise |

Both `[propext, Classical.choice, Quot.sound]`.

The audit's verdict, with the sizes worked out at `H ≍ N`, `T ≍ K ≍ exp((log x)^{1/10})`,
`d - 1 = c₀/(2log⁹K)` and `log x / log⁹K = (log x)^{1/10}`:

| edge | growth from the abscissa | damping | net exponent of `(log x)^{1/10}` |
|---|---|---|---|
| left vertical | `exp(+(9c₀/16)·(log x)^{1/10})` if `σmax` is global | none | `+8c₀/16` — **fatal**, now repaired |
| left vertical, repaired | none (constant at `c`) | the saving | `-c₀/16` |
| horizontal | `exp(+(c₀/2)·(log x)^{1/10})` | `T^{-(j+1)}` | `c₀/2 - (j+1) < 0` since `c₀ ≤ 1` |
| truncation | `exp(+(c₀/2)·(log x)^{1/10})` | `T^{-1}` | `c₀/2 - 1 < 0` since `c₀ ≤ 1` |

So the horizontal edges and the truncation error survive their abscissa growth — but only because
`zeroFreeConst ≤ 1`, and only when `σmax` is taken to be `d` rather than a fixed larger number.  At
`σmax = 2` the growth is `(N+H)^{1}` and every term is worse than trivial.

This changes the shape of the assembly.  `exists_norm_tsum_moebius_smoothWeight_le` fixes one
constant `C` and then quantifies over `d`; but `d = d(K)` and the constants must move with it, so
the correct statement supplies the three decay constants as hypotheses rather than existentials.
That is what the sharp lemmas above provide, and it is why the earlier `∃ C, ∀ K` form has to be
replaced rather than instantiated.

#### The four-edge inequality, sharp form — `RHTower/Sieve/PerronSharpSubstitution.lean`

`norm_tsum_moebius_smoothWeight_le_sharp` — unconditional,
`[propext, Classical.choice, Quot.sound]`:

    ‖ 2π ∑ₙ μ(n)·w(n) ‖ ≤ 2·Md·C₁/T
                          + 2·Mh·C₂·(d-c)/T^{j+1}
                          + Mc·( 2(N+H)^c/c + 2C₃ )

with `C₁`, `C₂` decay constants of the cutoff's transform at abscissa `d` (orders `2` and `j+1`) and
`C₃` at abscissa `c` (order `2`), all supplied as hypotheses.

This replaces `exists_norm_tsum_moebius_smoothWeight_le`, which fixed one constant before
quantifying over the geometry.  That form is not merely lossy — with `d = d(K)` and `c = c(K)` the
constants must move with `K`, so no instantiation of it can be used.  The three constants also had
to be separated: `C₁` and `C₂` differ only in the decay order, but `C₃` must be taken at `c`, and
conflating it with the others is exactly the defect the previous section recorded.

Where this leaves the route: every analytic ingredient is proved, and the inequality is now in a
form whose every constant can be instantiated at the concrete rectangle.  The remaining work is to
re-do the concrete instantiation (`MoebiusContourBound`, which used the superseded form with
`σmax = 2`) against this statement, and then the elementary optimisation in `K`.

#### The decay constant, abscissa dependence exposed — `RHTower/Sieve/MellinAbscissaDecay.lean`

The repair of the previous two sections needs one more ingredient: the three decay constants have to
be *known* to be of size `(N+H)^{abscissa}`, and `exists_bound_mellin_smoothWeight` hides that inside
an existential.  Hiding it is exactly why the constant became unusable once the abscissa started
moving with the contour parameter.

| statement | content |
|---|---|
| `exists_bound_mellin_smoothWeight_abscissa` | `\|Im s\|^{j+1}·‖W(s)‖ ≤ C·(N+H+1)^{Re s}`, `C` free of the abscissa |
| `exists_bound_mellin_smoothWeight_upto` | the same up to a given abscissa `σ`, with the factor `(N+H+1)^σ` |

Both `[propext, Classical.choice, Quot.sound]`.

The abscissa dependence can only take this form, and seeing why makes the earlier defect obvious in
hindsight: the Mellin integrand carries `x^{Re s}` and `x ≤ N+H+1` on the cutoff's support, so the
abscissa enters through exactly one factor `(N+H+1)^{Re s}` and nothing else.  A constant quantified
over a *range* of abscissae therefore carries the power at the top of the range, whatever the point
where it is used.

With this, the three constants of `norm_tsum_moebius_smoothWeight_le_sharp` are instances of a single
`C`:

    C₁ = C · (N+H+1)^d   (order 2, at the right abscissa)
    C₂ = C · (N+H+1)^d   (order j+1, at the right abscissa)
    C₃ = C · (N+H+1)^c   (order 2, at the left abscissa)

and `C₃`'s power is `(N+H+1)^c`, which is the same size as the main term `(N+H)^c` it is added to —
so the left edge carries the saving, as required.

#### The concrete rectangle, sharp — `RHTower/Sieve/MoebiusContourBoundSharp.lean`

`exists_norm_tsum_moebius_smoothWeight_le_concrete_sharp` — unconditional,
`[propext, Classical.choice, Quot.sound]`.  Same geometry as the superseded
`MoebiusContourBound`, but each decay constant is taken at the abscissa where it is used:

    ‖ 2π ∑ₙ μ(n)·w(n) ‖ ≤ 2·R(K)·C·(N+H+1)^{d(K)} / T(K)
                          + 2·E(K)·C'·(N+H+1)^{d(K)}·(d(K)-c(K)) / T(K)^{j+1}
                          + max(M₀,E(K))·( 2(N+H)^{c(K)}/c(K) + 2C·(N+H+1)^{c(K)} )

for all `K ≥ K₀`, with `C`, `C'`, `M₀` independent of `K`.

The left edge is now uniformly of size `(N+H)^{c(K)}` — both the main term and the tail constant —
so it carries the saving `exp(-c₀ log(N+H)/(16 log⁹K))`.  The first two terms carry
`(N+H)^{d(K)} = (N+H)·exp(c₀ log(N+H)/(2 log⁹K))`, a growth of the same shape but with the opposite
sign, damped by `T(K)^{-1}` and `T(K)^{-(j+1)}` respectively.

Both the superseded and the sharp version are kept: the earlier one is a true statement with global
constants, and the difference between them is precisely the point recorded three sections above —
which is worth being able to see side by side rather than only in prose.

What is left is arithmetic on this inequality with `K = contourParam (N+H)`, using
`le_saving_exponent` for the third term and the crude `c₀ ≤ 1` comparison for the first two.

#### Substituting the balanced parameter — `RHTower/Sieve/SavingSubstitution.lean`

| statement | content |
|---|---|
| `zeroFreeConst_le_half` | `c₀ ≤ 1/2` |
| `rpow_leftAbscissa_le_saving` | `y^{c(contourParam x)} ≤ y·exp(-c₀(log x)^{1/10}/8192)` for `log y ≥ log x` |

Both `[propext, Classical.choice, Quot.sound]`.

The second handles **both** parts of the left-edge term at once — the main term carries `(N+H)^c`
and the tail constant carries `(N+H+1)^c`, and the hypothesis is only `log y ≥ log x`, so the same
lemma covers `y = N+H` and `y = N+H+1` with `x = N+H`.  That the saving is stated at `x` while the
power is at `y` is what makes this work: the exponent is monotone in `log y`, so a larger `y` gives
a *better* saving, not a worse one.

`zeroFreeConst ≤ 1/2` is needed and `≤ 1` is not.  The truncation error carries growth
`exp(c₀·(log x)^{1/10}/2)` against damping `exp(-(log x)^{1/10})`, so the net exponent is
`c₀/2 - 1`; with only `c₀ ≤ 1` this is `≤ -1/2` — fine — but the horizontal edges at `j = 0` give
`c₀/2 - 1` as well, and the earlier audit's margin was stated as `< 0` without a rate.  With
`c₀ ≤ 1/2` every net exponent is at most `-3/4`, which is a rate and not just a sign.

(The true value is `c₀ = (e^{-11/2}/128)^4 ≈ 10^{-18}`, so the real margins are enormous; the point
of proving the crude bound is that it is what the inequalities can use.)

#### The right edge at the balanced parameter — `RHTower/Sieve/GrowthSubstitution.lean`

| statement | content |
|---|---|
| `rpow_rightAbscissa` | `x^{d(K)} = x·exp( c₀·log x / (2 log⁹K) )` |
| `rpow_rightAbscissa_le` | at `K = contourParam x`: `≤ y·exp( c₀·(log x)^{1/10} )` when `log y ≤ 2 log x` |
| `exp_div_four_le_truncHeight` | `T(contourParam x) ≥ exp((log x)^{1/10})/4` once `(log x)^{1/10} ≥ 2` |

All `[propext, Classical.choice, Quot.sound]`.

Together these give, for the truncation error's ratio,

    (N+H+1)^{d(K)} / T(K)  ≤  4·(N+H+1)·exp( (c₀ - 1)·(log(N+H))^{1/10} )

and with `c₀ ≤ 1/2` the exponent is at most `-(1/2)(log(N+H))^{1/10}`.  The horizontal edges carry
`T(K)^{-(j+1)}` instead and so are at least as good.

Two hypotheses in `rpow_rightAbscissa_le` are worth noting because they are what ties the two sides
together.  `log y ≤ 2 log x` is what lets the growth at `y = N+H+1` be measured against the saving's
`x = N+H`; it holds for `N+H ≥ 2` and is the only place the two arguments have to be compared.  And
the bound uses `log K ≥ (log x)^{1/10}` — the *lower* bound on `log(contourParam x)` — whereas the
saving used the upper bound.  Both directions of the squeeze proved in `ContourParameterChoice` are
therefore used, one per side of the contour.

#### The edge bounds at the balanced parameter — `RHTower/Sieve/EdgeBoundAtChoice.lean`

| statement | content |
|---|---|
| `log_contourParam_le_two` | `log K ≤ 2t` at `K = contourParam x`, `t = (log x)^{1/10}` |
| `log_contourParam_pow_le` | `log⁹K ≤ 512 t⁹` |
| `invZetaRightBound_contourParam_le` | `≤ e^{22/4}(1 + 1024 t⁹/c₀)` |
| `invZetaEdgeBound_contourParam_le` | `≤ 2e^{22/4}(1 + 1024 t⁹/c₀)(5/2 + 2t)` |

All `[propext, Classical.choice, Quot.sound]`.

Both edge bounds are now explicit polynomials in the single variable `t`, of degrees `9` and `10`.
Every quantity in the contour bound is therefore a function of `t` alone, apart from the trivial
size `N+H`:

| term | shape in `t` |
|---|---|
| truncation | `(N+H+1)·poly₉(t)·4·exp((c₀-1)t)` |
| horizontal | `(N+H+1)·poly₁₀(t)·4^{j+1}·exp((c₀-(j+1))t)·(d-c)` |
| left edge | `(N+H+1)·poly₁₀(t)·exp(-c₀t/8192)` |

with `c₀ ≤ 1/2`, so each exponential has a strictly negative rate.  The remaining step is the single
elementary fact that a polynomial times a decaying exponential tends to zero, applied three times,
and the conclusion `∑ₙ μ(n)w(n) = o(N+H)` follows.

#### Polynomial against exponential — `RHTower/Sieve/PolyExpDecay.lean`

| statement | content |
|---|---|
| `tendsto_pow_mul_exp_neg_mul` | `t^n·exp(-κt) → 0` for every `n` and every `κ > 0` |
| `tendsto_poly9_mul_exp_neg` | `(1 + a t⁹)·exp(-κt) → 0` |
| `tendsto_polyEdge_mul_exp_neg` | `(1 + a t⁹)(b + ct)·exp(-κt) → 0` |

All `[propext, Classical.choice, Quot.sound]`.

The two composite forms are exactly the shapes the two edge bounds take at the balanced parameter
(`invZetaRightBound` and `invZetaEdgeBound` respectively), so each term of the contour bound is
covered by one of them.  Note that no sign or size hypothesis on `a`, `b`, `c` is needed — the
statements are limits, not inequalities, so the coefficients are unrestricted reals and the
constants coming out of the corpus's edge estimates can be substituted without further checks.

This is the last analytic ingredient.  Every factor in

    ‖ 2π ∑ₙ μ(n)·w(n) ‖  ≤  (N+H+1) · [ three terms, each poly(t)·exp(-κt) with κ ≥ 1/2 ]

is now either the trivial size `N+H+1` or a quantity proved to tend to zero, so the bound is
`o(N+H)`.

#### The decay constant, uniform in the cutoff — `RHTower/Sieve/MellinDecayUniform.lean`

`exists_bound_mellin_smoothWeight_uniform_all` — unconditional,
`[propext, Classical.choice, Quot.sound]`:

    |Im s|^{j+1}·‖W(s)‖  ≤  Cⱼ · H^{-(j+1)} · (N+H+1)^{j+1} · (N+H+1)^{Re s}

with `Cⱼ` depending on the order alone.

This is needed for a reason the earlier modules concealed.  Every constant so far was produced with
the cutoff `(N, H)` already fixed, which is harmless while only the contour parameter moves — but the
final statement lets `N → ∞`, and a constant depending on `N` says nothing there.  The dependence
turns out to be entirely explicit: the only genuinely unknown quantity is the bound on the iterated
derivatives of the cutoff *profile*, and `exists_bound_iteratedDeriv_smoothWeight_uniform` already
supplies that uniformly in `N` and `H`.  Everything else is the visible factor
`H^{-(j+1)}(N+H+1)^{j+1}`.

At `H ≍ N` that factor is bounded: with `H = N` and `N ≥ 1` it is at most `3^{j+1}`.  So the
constants of the contour bound are genuinely absolute once the smoothing width is proportional to
the cutoff — which is the regime in which the smoothed sum approximates `∑_{n≤N} μ(n)` anyway.

This closes the last dependence that would have obstructed the limit `N → ∞`.

#### Absolute constants at proportional smoothing — `RHTower/Sieve/MellinDecayDiagonal.lean`

`exists_bound_mellin_smoothWeight_diag` — unconditional,
`[propext, Classical.choice, Quot.sound]`: for the cutoff `smoothWeight N N` and every `N ≥ 1`,

    |Im s|^{j+1}·‖W(s)‖  ≤  Cⱼ · (2N+1)^{Re s}

with `Cⱼ` depending on the order alone.

Taking `H = N` turns the explicit factor `H^{-(j+1)}(N+H+1)^{j+1}` into `((2N+1)/N)^{j+1} ≤ 3^{j+1}`,
a number.  So at proportional smoothing every constant in the contour bound is absolute, and the
only cutoff dependence anywhere is the honest factor `(2N+1)^{Re s}` — which is the term the saving
acts on.

`H = N` is not a convenience: the smoothed sum only approximates `∑_{n≤x} μ(n)` when the smoothing
width is comparable to the cutoff, so this is the regime the argument has to work in, and it is the
regime in which the constants behave.

With this the contour bound has no remaining hidden dependence on `N`:

    ‖ 2π ∑ₙ μ(n)·w(n) ‖  ≤  (2N+1) · [ three explicit terms in t = (log 2N)^{1/10} ]

each term a polynomial in `t` times `exp(-κt)` with `κ ≥ 1/2`, and each such product proved to tend
to zero.

#### The contour bound, uniform in the cutoff — `RHTower/Sieve/MoebiusContourBoundDiag.lean`

`exists_norm_tsum_moebius_smoothWeight_le_diag` — unconditional,
`[propext, Classical.choice, Quot.sound]`.  The same inequality as the sharp version at `H = N`,
but with the quantifiers in the order the limit needs:

    ∃ C C' M₀ K₀,  ∀ N ≥ 1,  ∀ K ≥ K₀,   ‖ 2π ∑ₙ μ(n)·w(n) ‖  ≤  …

The constants now stand **outside** the quantifier over the cutoff.  That is the whole content of
the specialisation, and it was not available before `MellinDecayDiagonal`: every earlier version
fixed `(N, H)` before producing its constants, so letting `N → ∞` would have compared quantities
that move with `N`.

Worth recording is how little had to change.  The geometric scaffolding — the rectangle, its
zero-freeness, the three bounds on `invZeta`, the continuity of the left edge — is a function of the
contour parameter `K` alone and never mentions the cutoff.  So only the three decay constants needed
to be made uniform, and the proof is otherwise identical to the sharp version.  The separation of
"geometry depends on `K`" from "size depends on `N`" is what makes the two limits independent.

Also note `K₀` is absolute: it comes from `exists_zero_free_box` and `exists_bound_invZeta_low_box`,
both of which are statements about `ζ` with no cutoff in them.  So the same `K₀` works for every `N`,
and `K = contourParam (2N)` exceeds it for all large `N`.

#### The left-edge term collapses — `RHTower/Sieve/LeftEdgeTerm.lean`

| statement | content |
|---|---|
| `half_le_leftAbscissa_contourParam` | `c(contourParam x) ≥ 1/2` as soon as `log x ≥ 1` |
| `leftEdge_term_le` | `M·(2x^c/c + 2C·y^c) ≤ M·(4+2C)·y·exp(-c₀(log x)^{1/10}/8192)` |

Both `[propext, Classical.choice, Quot.sound]`.

The whole left-edge term — both its pieces — is now the trivial size `y` times the saving.  The two
pieces are `(2N)^{c}` divided by the abscissa and the tail constant times `(2N+1)^{c}`, and it is
`rpow_leftAbscissa_le_saving`'s tolerance of `log y ≥ log x` that lets one lemma serve both.

The abscissa bound is cheaper than expected and worth recording, because a weaker version would have
forced an astronomically large threshold on `N`.  `c(K) ≥ 1/2` needs only `c₀/(16 log⁹K) ≤ 1/2`, and
`log K ≥ (log x)^{1/10} ≥ 1` already gives `log⁹K ≥ 1`; with `c₀ ≤ 1/2` the quotient is at most
`1/32`.  So `log x ≥ 1` suffices — no condition of the form `(log x)^{1/10} ≥ 3`, which would have
meant `x ≥ e^{59049}`.

This is where `zeroFreeConst_le_half` earns its place a second time: with only `c₀ ≤ 1` the quotient
bound would be `1/16`, still enough here, but the same constant is what gives the truncation term a
rate rather than a sign.

#### The right-hand terms collapse — `RHTower/Sieve/RightSideTerm.lean`

`rightSide_term_le` — unconditional, `[propext, Classical.choice, Quot.sound]`:

    A · y^{d(contourParam x)} / T(contourParam x)  ≤  4·A·y·exp( -(1 - c₀)·(log x)^{1/10} )

for `A ≥ 0`, `log y ≤ 2 log x`, `(log x)^{1/10} ≥ 2`.

One lemma covers both the truncation error and the horizontal edges, because at `j = 0` they have
the same shape — a coefficient times `y^{d(K)}` over one power of the truncation height.  Taking
`j = 0` is not a loss: the exponent is already `1 - c₀ ≥ 1/2`, and larger `j` only improves it while
complicating the cast arithmetic.

With this all three terms of the contour bound are of the form

    (trivial size) × (polynomial in t) × exp(-κ t),      κ ≥ 1/2,

namely `exp(-c₀t/8192)` for the left edge and `exp(-(1-c₀)t)` for the other two.  The two rates are
very different — the left edge decays far more slowly — but both are positive, and that is all the
limit needs.

That asymmetry is the honest shape of the argument: the saving bought by moving the contour left is
tiny (`c₀/8192` with `c₀ ≈ 10^{-18}`), while the truncation and horizontal edges are damped by the
full height. The binding constraint on the whole method is therefore the left edge, exactly as the
classical account says.

#### The three terms combined — `RHTower/Sieve/MoebiusCombinedBound.lean`

| statement | content |
|---|---|
| `exp_right_le_exp_left` | `exp(-(1-c₀)t) ≤ exp(-c₀t/8192)` — the slower rate dominates |
| `gap_le_one` | `d(K) - c(K) ≤ 1` |
| `combined_terms_le` | all four summands ≤ `(x+1)·[8RC + 8EC' + max(M₀,E)(4+2C)]·exp(-c₀t/8192)` |

All `[propext, Classical.choice, Quot.sound]`.

The whole right-hand side of the contour bound is now a **single** product: trivial size, times a
coefficient built from the edge bounds, times one exponential.  Reducing to one exponential is what
`exp_right_le_exp_left` buys, and it is legitimate only because `c₀ ≤ 1/2` makes
`c₀/8192 ≤ 1 - c₀`; with `c₀` close to `1` the left edge would decay *faster* than the truncation
error and the bound would have to keep both rates.

`gap_le_one` needed a second bound the first draft omitted: the gap is
`c₀/(2log⁹K) + c₀/(16log⁹K)`, and bounding only the first summand leaves the second uncontrolled.
Both are at most `1/54`, so the gap is at most `1/27`.

What remains is to substitute the polynomial majorants for `R(K)` and `E(K)`
(`EdgeBoundAtChoice`), giving a bound of the form `(x+1)·P(t)·exp(-c₀t/8192)` with `P` an explicit
polynomial, and then apply `tendsto_polyEdge_mul_exp_neg`.

#### The coefficient majorised — `RHTower/Sieve/CoeffMajorant.lean`

| statement | content |
|---|---|
| `coeffMajorant` | the explicit polynomial majorant of `8RC + 8EC' + max(M₀,E)(4+2C)` |
| `coeff_le_coeffMajorant` | the coefficient is at most it, at the balanced parameter |
| `tendsto_coeffMajorant_mul_exp_neg` | `coeffMajorant(t)·exp(-κt) → 0` for every `κ > 0` |

Both theorems `[propext, Classical.choice, Quot.sound]`.

The majorant is chosen to be a sum of exactly the three shapes already proved to decay against an
exponential — `(1 + a t⁹)`, `(1 + a t⁹)(5/2 + 2t)`, and a constant — so its limit follows by
`Tendsto.add` from `PolyExpDecay` with no new analysis.  Writing the majorant to fit the available
lemmas rather than expanding the polynomial and proving a general degree-ten statement is what keeps
this step short.

The `max` is handled by `max M₀ E ≤ M₀ + E`, which is where both `M₀ ≥ 0` and `E ≥ 0` are used; the
second is `invZetaEdgeBound_nonneg`, and without it the majorisation would fail for a reason that has
nothing to do with the analysis.

So the contour bound is now

    ‖ 2π ∑ₙ μ(n)·w(n) ‖  ≤  (2N+1) · coeffMajorant(t) · exp(-c₀ t / 8192),      t = (log 2N)^{1/10},

with the second factor proved to tend to zero.  The remaining work is bookkeeping: instantiate the
diagonal contour bound at `K = contourParam (2N)`, check the four numeric side conditions on `N`,
and read off `∑ₙ μ(n)·w(n) = o(N)`.

#### The smoothed sum against the majorant — `RHTower/Sieve/MoebiusMajorantBound.lean`

`exists_norm_tsum_moebius_smoothWeight_le_majorant` — unconditional,
`[propext, Classical.choice, Quot.sound]`:

    ‖ 2π ∑ₙ μ(n)·w(n) ‖ ≤ (2N+1)·coeffMajorant(t)·exp(-c₀t/8192),    t = (log 2N)^{1/10},

for `N ≥ 1` with `log 2N ≥ 1`, `t ≥ 2`, and `contourParam (2N) ≥ K₀`.  The constants `C`, `C'`, `M₀`
and the threshold `K₀` are absolute.

Two side conditions were cheaper than they first looked.

`gap_le_one` was stated with `3 ≤ log K`, which would have forced `t ≥ 3` and hence
`log 2N ≥ 3^10 = 59049`.  But the gap is `c₀(1/2 + 1/16)/log⁹K`, so `1 ≤ log K` already gives
`≤ 1/4 + 1/32 < 1` using `c₀ ≤ 1/2`.  Weakening the hypothesis keeps the threshold at `t ≥ 2`, which
is what `exp_div_four_le_truncHeight` needs anyway.

`log(2N+1) ≤ 2 log(2N)` reduces to `2N+1 ≤ (2N)²`, true for every `N ≥ 1`; it is the only place the
two arguments of the saving and the growth have to be reconciled, and it costs nothing.

The bound is now a product of three factors: the trivial size, and two whose product tends to zero.

### The smoothed Möbius sum is `o(N)` — `RHTower/Sieve/MoebiusSmoothLittleO.lean`

`tendsto_norm_tsum_moebius_smoothWeight_div` — unconditional,
`[propext, Classical.choice, Quot.sound]`:

    ‖ ∑ₙ μ(n)·w_N(n) ‖ / (2N+1)  →  0     as  N → ∞,      w_N = smoothWeight N N.

This closes the contour argument.  The chain, every link unconditional and axiom-clean:

| step | module |
|---|---|
| `1/ζ` corrected at the pole | `InvZetaRegular` |
| a zero-free rectangle at every height | `ZeroFreeRectangle`, `ZeroFreeConcreteRect` |
| Cauchy on the truncated rectangle | `InvZetaProductShift` |
| the four edges bounded | `HorizontalEdgeBound`, `VerticalMassSharp`, `TruncationError`, `EdgeBoundsSharp` |
| `‖1/ζ‖` on each edge | `InvZetaLowBox`, `InvZetaSegmentBound`, `HalfComparison`, `InvZetaLeftEdge`, `InvZetaLeftLine`, `InvZetaEdgeBounds` |
| decay constants where they are used | `MellinAbscissaDecay`, `MellinDecayUniform`, `MellinDecayDiagonal` |
| the Perron identity and the four-edge combination | `PerronEdgeAssembly`, `PerronSharpSubstitution` |
| the concrete rectangle | `MoebiusContourBoundSharp`, `MoebiusContourBoundDiag` |
| the balanced parameter | `ContourParameterChoice`, `SavingSubstitution`, `GrowthSubstitution` |
| the terms collapsed | `LeftEdgeTerm`, `RightSideTerm`, `MoebiusCombinedBound` |
| polynomial against exponential | `PolyExpDecay`, `EdgeBoundAtChoice`, `CoeffMajorant` |
| the limit | `MoebiusMajorantBound`, `MoebiusSmoothLittleO` |

The statement is about the *smoothed* sum.  Passing to `∑_{n≤x} μ(n) = o(x)` needs one further and
entirely elementary step — comparing the smoothed sum with the sharp one, which costs `O(H) = O(N)`
per unit of smoothing and so requires the smoothing to be taken narrower than proportional, at the
price of a weaker saving.  That is a separate argument and is not claimed here.

Three findings from this route are worth carrying forward:

1. Mathlib's junk value at `s = 1` makes `fun s => (ζ s)⁻¹` genuinely discontinuous exactly where the
   contour crosses.  The correction `invZeta s = (s-1)·G(s)⁻¹` needs no case split, and the *pole* is
   what supplies nonvanishing at the one point the line argument cannot reach.
2. A decay constant quantified over an abscissa *range* carries `(N+H)^{top of range}`.  When the
   range straddles `1` this is nine times the saving's exponent and the bound becomes worse than
   trivial — a defect that type-checks and looks harmless.
3. The binding constraint is the left edge, whose saving is `c₀/8192` with `c₀ ≈ 10^{-18}`, while the
   other edges are damped by the full truncation height.  The formalisation reproduces the classical
   bottleneck rather than a different one.

#### The smoothed sum against the sharp sum — `RHTower/Sieve/SmoothVsSharp.lean`

`norm_tsum_smoothWeight_sub_sum_le` — unconditional,
`[propext, Classical.choice, Quot.sound]`:

    ‖ ∑ₙ μ(n)·w(n) - ∑_{n ≤ N} μ(n) ‖  ≤  H + 1.

The cutoff is `1` below `N` and `0` above `N+H`, so the two sums agree outside the transition
window, where each summand has modulus at most `1`; the window holds at most `H+1` integers.  No
analysis enters — the whole proof is `tsum_eq_sum` on the finite support, `Finset.sum_Ico_consecutive`
to split off the agreeing range, and a floor computation for the count.

This is the step that decides what the contour argument is worth for the *sharp* sum, and it makes
the trade explicit.  At proportional smoothing `H = N` the comparison costs `O(N)` and says nothing.
To get `∑_{n≤x} μ(n) = o(x)` the smoothing must be narrower, `H = N/L`, and then the decay constants
grow like `L^{j+1}` — which the uniform bound `exists_bound_mellin_smoothWeight_uniform_all` already
tracks, since its cutoff dependence is the explicit factor `H^{-(j+1)}(N+H+1)^{j+1}`.

So the two requirements pull against each other and there is room between them: `L` subpolynomial,
say `L = exp((log N)^{1/20})`, makes the comparison error `N·exp(-(log N)^{1/20})` while costing only
a subpolynomial factor against the saving `exp(-c₀(log N)^{1/10}/8192)`.  The contour bound at
`H = N/L` is not yet assembled — `MoebiusContourBoundDiag` is stated at `H = N` — so this is a
statement about what remains, not a claim that it is done.

#### The contour bound at arbitrary smoothing width — `RHTower/Sieve/MoebiusContourBoundGeneral.lean`

`exists_norm_tsum_moebius_smoothWeight_le_general` — unconditional,
`[propext, Classical.choice, Quot.sound]`.  The same bound as the diagonal version, for **every**
`H > 0`, with the smoothing width entering only through the explicit factors

    C/H² · (N+H+1)²      (the order-two constants, right and left edges)
    C'/H · (N+H+1)       (the order-one constant, horizontal edges)

and `C`, `C'`, `M₀`, `K₀` absolute.  (`exists_bound_mellin_smoothWeight_uniform_upto`, added to
`MellinDecayUniform`, is what supplies these.)

This is the form in which the smoothing width becomes a free parameter, and it makes the trade
recorded in the previous section quantitative rather than heuristic.  Writing `H = N/L`:

| requirement | constraint on `L` |
|---|---|
| the sharp/smooth comparison `H + 1` is `o(N)` | `L → ∞` |
| `H^{-2}(N+H+1)² ≍ L²` does not swamp the saving | `L² ≪ exp(c₀(log N)^{1/10}/8192)` |

Both hold for `L = exp((log N)^{1/20})`, with room to spare — the second constraint permits `L` up
to `exp(c₀(log N)^{1/10}/16384)`, and `(log N)^{1/20}` is far below that.

Note the diagonal version is not superseded: at `H = N` the constants are absolute numbers rather
than functions of `L`, which is what made `MoebiusSmoothLittleO` clean.  The general version pays
`L²` for the freedom to choose `H`.

#### The cost of narrow smoothing — `RHTower/Sieve/WidthFactor.lean`

| statement | content |
|---|---|
| `width_ratio_le` | `(N+H+1)/H ≤ L + 2` whenever `H ≥ 1` and `N/H ≤ L` |
| `sq_width_factor_le` | `C/H²·(N+H+1)² ≤ C·(L+2)²` |
| `width_factor_le` | `C'/H·(N+H+1) ≤ C'·(L+2)` |

All `[propext, Classical.choice, Quot.sound]`.

The smoothing width enters the contour bound only as `((N+H+1)/H)^{j+1}`, and that ratio is `L + 2`
at worst: the `+H` contributes exactly `1` and the `+1` contributes `1/H ≤ 1`.  So narrowing the
smoothing by a factor `L` costs `L^{j+1}` and nothing else — no interaction with the contour geometry,
no dependence on `N` beyond the ratio.

The hypothesis `H ≥ 1` is what makes the `+1` harmless, and it is free in the intended regime
(`H = N/L` with `L` subpolynomial, so `H → ∞`).

Substituting these into the general contour bound turns its cutoff dependence into the single
polynomial factor `(L+2)²`, which is the last quantity that has to be weighed against the saving.

#### The contour bound in terms of the smoothing ratio — `RHTower/Sieve/MoebiusContourBoundRatio.lean`

`exists_norm_tsum_moebius_smoothWeight_le_ratio` — unconditional,
`[propext, Classical.choice, Quot.sound]`.  For all `N > 0`, `H ≥ 1`, `L ≥ N/H` and `K ≥ K₀`:

    ‖ 2π ∑ₙ μ(n)·w(n) ‖ ≤ 2·R(K)·C(L+2)²·(N+H+1)^{d(K)} / T(K)
                          + 2·E(K)·C'(L+2)·(N+H+1)^{d(K)}·(d(K)-c(K)) / T(K)
                          + max(M₀,E(K))·( 2(N+H)^{c(K)}/c(K) + 2C(L+2)²(N+H+1)^{c(K)} )

with `C`, `C'`, `M₀`, `K₀` absolute.

The cutoff now enters in exactly two ways: the trivial sizes `(N+H)^{c(K)}` and `(N+H+1)^{d(K)}`,
which the saving and growth lemmas already handle, and the single polynomial `(L+2)²` paid for
narrowing the smoothing.  This is structurally the diagonal bound with one extra factor, so the
collapse lemmas `leftEdge_term_le` and `rightSide_term_le` apply unchanged.

The whole substitution is one `gcongr` — the width factors are multiplied by norms and by positive
powers throughout, so monotonicity carries them into every term without case analysis.  Setting the
positivity facts up beforehand is what makes that possible; the geometric facts needed
(`T(K) ≥ 1`, `d(K) - c(K) ≥ 0`) follow from `K ≥ 5` alone, which is why `K₀` is enlarged to
`max K₀ 5` rather than carrying `log K ≥ 3` down from the general bound.

#### The ratio bound against the majorant — `RHTower/Sieve/MoebiusMajorantRatio.lean`

`exists_norm_tsum_moebius_smoothWeight_le_majorant_ratio` — unconditional,
`[propext, Classical.choice, Quot.sound]`:

    ‖ 2π ∑ₙ μ(n)·w(n) ‖ ≤ (N+H+1)·coeffMajorant(C(L+2)², C'(L+2), M₀, t)·exp(-c₀t/8192)

for `N > 0`, `H ≥ 1`, `L ≥ N/H`, `log(N+H) ≥ 1`, `t = (log(N+H))^{1/10} ≥ 2`, and
`contourParam(N+H) ≥ K₀`.

The price of narrow smoothing needed no new argument at all.  `combined_terms_le` and
`coeff_le_coeffMajorant` take the two contour constants as *parameters*, so substituting `C(L+2)²`
and `C'(L+2)` makes the ratio bound an instance of the very chain that produced the diagonal one —
the entire collapse is reused verbatim.

That is the payoff of having stated the collapse lemmas with abstract constants rather than at the
concrete values.  Had they been specialised, every step from `LeftEdgeTerm` onward would have had to
be redone with the extra factor threaded through.

`L` now appears in exactly one place: inside the polynomial coefficient.  Choosing `H = N/L` with
`L = exp((log N)^{1/20})` makes that coefficient `exp(2(log N)^{1/20})·poly(t)`, still beaten by
`exp(-c₀(log N)^{1/10}/8192)` since `1/20 < 1/10`; and the sharp/smooth comparison then costs
`H + 1 ≍ N·exp(-(log N)^{1/20})`.

#### Linear growth against quadratic decay — `RHTower/Sieve/ExpQuadraticDecay.lean`

| statement | content |
|---|---|
| `rpow_twentieth_sq` | `(u^{1/20})² = u^{1/10}` |
| `tendsto_exp_two_sub_sq` | `exp(2v - κv²) → 0` for `κ > 0` |
| `tendsto_poly_exp_two_sub_sq` | `(1+a(v²)⁹)(b+cv²)·exp(2v)·exp(-κv²) → 0` |

All `[propext, Classical.choice, Quot.sound]`.

The first identity is what makes the whole comparison elementary.  The price of narrow smoothing is
`exp(2(log N)^{1/20})` and the saving is `exp(-c₀(log N)^{1/10}/8192)`; writing `v = (log N)^{1/20}`
turns the second exponent into `-c₀v²/8192`, so the two are a *linear* and a *quadratic* function of
one variable, and no asymptotic machinery is needed beyond `exp(2v - κv²) ≤ exp(-v)` for
`v ≥ 3/κ`.

That is the reason `1/20` is the right smoothing exponent.  Any exponent strictly below `1/10`
works, but taking exactly half turns the comparison into the quadratic one; a different choice would
give `exp(2v^θ - κv)` with `θ < 1` and require a genuine growth comparison instead of a `nlinarith`
step.

The third statement splits the exponential as `exp(-κv²/2)·exp(2v - κv²/2)` — half the saving kills
the polynomial through the already-proved `tendsto_polyEdge_mul_exp_neg`, the other half kills the
price.  Splitting rather than fighting both factors at once is what lets the earlier lemma be
reused unchanged.

#### The smoothing width — `RHTower/Sieve/SmoothWidthChoice.lean`

    smoothRatio N = exp((log N)^{1/20}),      smoothWidth N = N / smoothRatio N.

| statement | content |
|---|---|
| `one_le_smoothRatio`, `smoothRatio_pos` | the ratio is a genuine factor ≥ 1 |
| `one_le_smoothWidth` | the width is at least `1` once `log N ≥ 1` |
| `smoothWidth_le` | the width is at most the cutoff |
| `div_smoothWidth` | `N / smoothWidth N = smoothRatio N`, so `L := smoothRatio N` is admissible |
| `tendsto_smoothRatio_atTop` | the ratio tends to infinity |
| `tendsto_smoothWidth_div` | `(smoothWidth N + 1)/N → 0` — the comparison error is `o(N)` |

All `[propext, Classical.choice, Quot.sound]`.

`one_le_smoothWidth` is the only one with content: it needs `exp((log N)^{1/20}) ≤ N`, which reduces
to `(log N)^{1/20} ≤ log N` — true for `log N ≥ 1` because raising a number `≥ 1` to a smaller
exponent decreases it.  That single inequality is what makes `H ≥ 1` free, which in turn is what
`WidthFactor` needs.

With this both requirements on the width are theorems rather than intentions:
`tendsto_smoothWidth_div` gives the sharp/smooth comparison, and `div_smoothWidth` supplies
`L = smoothRatio N` to the ratio bound, whose price `(L+2)²` is `exp(2(log N)^{1/20})` up to a
constant — exactly the quantity `ExpQuadraticDecay` weighs against the saving.

#### The two logarithmic variables compared — `RHTower/Sieve/LogComparison.lean`

| statement | content |
|---|---|
| `sq_le_logRpow` | `v² ≤ t` |
| `logRpow_le_two_sq` | `t ≤ 2v²` |

with `t = (log(N+H))^{1/10}`, `v = (log N)^{1/20}`, for `0 ≤ H ≤ N` and `log N ≥ 1`.  Both
`[propext, Classical.choice, Quot.sound]`.

The saving is expressed in `t` and the price in `v`, so nothing can be compared until the two are
related.  Since `N ≤ N+H ≤ 2N` they are, and both directions are used: the lower bound converts the
saving `exp(-c₀t/8192)` into `exp(-c₀v²/8192)`, which is what `ExpQuadraticDecay` weighs against
`exp(2v)`; the upper bound keeps the polynomial in `t` a polynomial in `v²`, which is what makes
`tendsto_poly_exp_two_sub_sq` applicable at all.

The constant `2` in the upper bound comes from `log 2 ≤ 1` and `2^{1/10} ≤ 2` — both crude, and both
harmless, since a constant factor on `v²` changes nothing in a quadratic-beats-linear comparison.

`H ≤ N` holds for `smoothWidth` by `smoothWidth_le`, and `0 ≤ H` because the ratio is positive.  So
both hypotheses are discharged by the previous module.

#### Monotonicity of the majorant, and the size of the ratio — `RHTower/Sieve/CoeffMajorantMono.lean`

| statement | content |
|---|---|
| `coeffMajorant_mono_t` | the majorant is increasing in its variable when its coefficients are nonnegative |
| `smoothRatio_add_two_le` | `L + 2 ≤ 3·exp(v)` |
| `zero_le_smoothRatio_add_two` | `0 ≤ L + 2` |

All `[propext, Classical.choice, Quot.sound]`.

These are what let the majorant's variable be changed from `t` to `v`.  Monotonicity means the
comparison `t ≤ 2v²` can be substituted straight into the majorant instead of expanding it; the
proof is a single `gcongr` once the coefficient nonnegativities are in context.

`M₀ ≥ 0` turned out not to be needed for monotonicity — `M₀` appears in the majorant only in the
constant term `M₀(4+2C)`, which does not involve `t` — so the hypothesis is dropped.  A small thing,
but it is the kind of surplus hypothesis that propagates into every call site if left in.

`L + 2 ≤ 3exp(v)` is immediate from `exp(v) ≥ 1`, and it is the only place the shape of
`smoothRatio` is used: everything downstream sees the ratio through this bound alone.

#### Scaling the majorant's constants — `RHTower/Sieve/CoeffMajorantScale.lean`

| statement | content |
|---|---|
| `coeffMajorant_mono_const` | the majorant is increasing in both its constants |
| `coeffMajorant_scale` | `coeffMajorant (C·E) (C'·E) M₀ a w ≤ E · coeffMajorant C C' M₀ a w` for `E ≥ 1` |

Both `[propext, Classical.choice, Quot.sound]`.

The second is what pulls the price of narrow smoothing out of the majorant altogether: the price
enters as `C(L+2)²` and `C'(L+2)`, both at most a constant times `exp(2v)`, and once it is outside
the majorant the remaining polynomial is the same one the diagonal case already handled.

The inequality is *not* an identity, and the reason is worth noting: the majorant has a constant
term `M₀(4+2C)` and a `4` inside its middle coefficient, neither of which scales with `E`.  Both
discrepancies contribute `4(E-1)` times something nonnegative — they happen to have the right
sign — so the statement holds, but it would fail with the inequality reversed.  The proof is
`nlinarith` on that difference, with the two nonnegative products supplied explicitly.

Neither `C ≥ 0` nor `C' ≥ 0` is needed for the scaling: `C` and `C'` appear on both sides in the
same positions, so only `E ≥ 1` and the nonnegativity of the `t`-dependent factors matter.

#### The majorant as a single product — `RHTower/Sieve/CoeffMajorantProd.lean`

`coeffMajorant_le_prod` — unconditional, `[propext, Classical.choice, Quot.sound]`:

    coeffMajorant C C' M₀ a (2w)  ≤  (1 + 512a·w⁹) · (b + c·w)

with `b`, `c` explicit in `C`, `C'`, `M₀`.

`tendsto_polyEdge_mul_exp_neg` handles a single product `(1 + a w⁹)(b + c w)`, while the majorant is
a *sum* of three pieces.  Bounding the sum by one product costs nothing, and the reason is
structural: the two `w`-dependent pieces already share the factor `1 + a w⁹`, and the constant piece
is at most that factor times itself because `1 + a w⁹ ≥ 1`.  The difference between the two sides is
exactly `(1 + a w⁹ - 1)·M₀(4+2C) ≥ 0`.

Evaluating at `2w` instead of `w` only replaces `a` by `512a` — `(2w)⁹ = 512w⁹` — so the factor-of-two
slack in `t ≤ 2v²` costs a constant in the polynomial's coefficient and nothing else.

`C' ≥ 0` is not needed: `C'` occurs on both sides in the same position.  With this the chain from
the ratio bound to `tendsto_poly_exp_two_sub_sq` is complete at the level of individual lemmas —
monotone in `t`, monotone in the constants, scale the constants out, bound the sum by a product.

#### The majorant in the variable `v` — `RHTower/Sieve/CoeffRatioBound.lean`

`coeffMajorant_ratio_le` — unconditional, `[propext, Classical.choice, Quot.sound]`:

    coeffMajorant (C(L+2)²) (C'(L+2)) M₀ a t · exp(-κt)
        ≤ (1 + 512a(v²)⁹)·(b + c·v²)·exp(2v)·exp(-κv²)

for `0 ≤ v`, `v² ≤ t ≤ 2v²`, `L + 2 ≤ 3exp(v)`, with `b`, `c` explicit in `C`, `C'`, `M₀`.

This is the four steps of the previous three modules run in order — monotone in `t`, monotone in the
constants, scale the constants out, bound the sum by a product — plus `exp(-κt) ≤ exp(-κv²)` from
`t ≥ v²`.  Both directions of `LogComparison` are used, one at the start and one at the end, which
is why that module needed both.

The right-hand side is now literally the expression `tendsto_poly_exp_two_sub_sq` is stated for, with
`a` replaced by `512a`.  So the pointwise majorisation and the limit fit together with no further
manipulation.

Each of the four steps required strictly fewer hypotheses than first written — `M₀ ≥ 0` for the
`t`-monotonicity, `C, C' ≥ 0` for the scaling, `C' ≥ 0` for the product bound — and dropping them
kept this assembly free of side conditions that would have had to be rediscovered here.

#### The majorant at the chosen width tends to zero — `RHTower/Sieve/CoeffRatioLimit.lean`

`tendsto_coeffMajorant_ratio` — unconditional, `[propext, Classical.choice, Quot.sound]`: at
`H = smoothWidth N`,

    coeffMajorant (C(L+2)²) (C'(L+2)) M₀ a t · exp(-κt)  →  0     as N → ∞,

for every `κ > 0` and nonnegative data, with `L = smoothRatio N` and `t = (log(N+H))^{1/10}`.

The proof is a squeeze between `0` and the pointwise bound of `CoeffRatioBound`, whose limit is
`tendsto_poly_exp_two_sub_sq` composed with `(log N)^{1/20} → ∞`.  Every hypothesis of the pointwise
bound holds eventually and each is already a theorem:

| hypothesis | source |
|---|---|
| `0 ≤ H ≤ N` | `smoothWidth_le`, positivity of the ratio |
| `v² ≤ t` | `sq_le_logRpow` |
| `t ≤ 2v²` | `logRpow_le_two_sq` |
| `L + 2 ≤ 3exp(v)` | `smoothRatio_add_two_le` |
| `0 ≤ L + 2` | `zero_le_smoothRatio_add_two` |

so nothing new about the smoothing had to be established here.

This is the last quantity in the ratio bound that was not yet known to vanish.  With it, the
contour bound at the chosen width is the trivial size `N+H+1` times something tending to zero,
which together with `norm_tsum_smoothWeight_sub_sum_le` and `tendsto_smoothWidth_div` is what a
statement about `∑_{n≤N} μ(n)` requires.

### `∑_{n ≤ N} μ(n) = o(N)` — `RHTower/Sieve/MoebiusSharpLittleO.lean`

`tendsto_norm_sum_moebius_div` — unconditional, `[propext, Classical.choice, Quot.sound]`:

    ‖ ∑_{n ≤ N} μ(n) ‖ / N  →  0     as N → ∞.

This is the sharp sum, not the smoothed one.  The statement two sections ago
(`tendsto_norm_tsum_moebius_smoothWeight_div`) was about `∑ₙ μ(n)w_N(n)` at proportional smoothing
and did **not** imply this; the passage needed the smoothing width to be narrowed, the contour bound
restated at arbitrary width, and the price of narrowing weighed against the saving.  That is what
the modules from `SmoothVsSharp` onward supply.

At `H = N/exp((log N)^{1/20})` the two competing requirements are both met:

| term | size | source |
|---|---|---|
| contour bound | `3N · coeffMajorant(t)·exp(-c₀t/8192) / 2π` | `MoebiusMajorantRatio`, `CoeffRatioLimit` |
| sharp/smooth comparison | `H + 1` | `SmoothVsSharp`, `tendsto_smoothWidth_div` |

and both are `o(N)`.

The whole development is now closed from the Riemann zeta function to a statement about `μ`, with no
hypothesis anywhere.  Of the forty-odd modules built for it, the three findings worth carrying
forward remain those recorded at the smoothed stage — mathlib's junk value at `s = 1`; the
abscissa-range trap in the decay constants; the left edge as the binding constraint — together with
a fourth from this stage:

4. Stating the collapse lemmas with *abstract* constants rather than at their concrete values is what
   let the entire chain from `LeftEdgeTerm` to `CoeffMajorant` be reused verbatim when the smoothing
   width became a parameter.  Specialising early would have cost a second development.

#### Novelty check

Mathlib on this toolchain (v4.32.2) contains **no** Prime Number Theorem and no Möbius summatory
asymptotic.  Searching `Mathlib/NumberTheory/` for `PrimeNumberTheorem`, `prime_number_theorem`, and
for any `Tendsto`/`IsLittleO`/asymptotic statement about `ArithmeticFunction.moebius` returns
nothing; the only hit is a comment in `Chebyshev.lean` noting that *parts* of that file were
upstreamed from the external PrimeNumberTheoremAnd project.  `PrimeCounting.lean` contains counting
definitions and elementary bounds, not an asymptotic.

So `tendsto_norm_sum_moebius_div` is not a re-derivation of an existing mathlib result.  It is a
corpus-owned theorem of independent value: `∑_{n≤x} μ(n) = o(x)` is equivalent to the Prime Number
Theorem, and the chain that produces it — smoothed Perron, truncated contour, zero-free region,
balanced parameter — is reusable for any Dirichlet series with a similar zero-free region.

#### The contour result reaches the card's objects — `RHTower/Sieve/MoebiusSignBalance.lean`

| statement | content |
|---|---|
| `moebius_trichotomy` | `μ(n) ∈ {-1, 0, 1}` |
| `sum_moebius_eq_card_sub` | `∑_{n∈s} μ(n) = #{n∈s : μ=1} - #{n∈s : μ=-1}` |
| `tendsto_card_moebius_sign_diff` | the two sign counts differ by `o(N)` |

All `[propext, Classical.choice, Quot.sound]`.

The card's objects are the *sign classes* `{m : μ(m) = ε}`, and `CoprimeProductSign.card_moebius_eq_ge`
bounds them from below.  The contour result now bounds their **difference** from above: since `μ`
takes only the values `-1, 0, 1`, the summatory function is exactly the difference of the two counts,
so `∑_{n≤N} μ(n) = o(N)` says the two sign classes have equal density.

That is a genuine, unconditional statement about the card's own objects, obtained without
Matomäki--Radziwiłł.  It does not replace the card's hard gate — the card asks for a *short-interval*
sign law, and equal density over `[1,N]` says nothing about `[x, x+h√x]` — but it is the first
upper-bound information the corpus has about these classes, to set against the lower bounds the
sieve layer already provides.

### Opening the Chebyshev route — `RHTower/Sieve/ZetaLogDerivRegular.lean`

The contour apparatus built for `1/ζ` transfers to `-ζ'/ζ`, whose summatory function is `ψ(x)`.
Mathlib already supplies the Dirichlet series identity
(`LSeries_vonMangoldt_eq_deriv_riemannZeta_div : LSeries Λ s = -ζ'(s)/ζ(s)` for `re s > 1`), and the
corpus already owns the local splitting at the pole (`logDeriv_zeta_eq`).

| statement | content |
|---|---|
| `zetaLogDerivReg` | the regular part `-G'/G` with `G = (s-1)ζ(s)` |
| `neg_logDeriv_riemannZeta_eq` | `-ζ'/ζ = 1/(s-1) + zetaLogDerivReg` off the pole |
| `differentiableAt_zetaLogDerivReg` | holomorphic wherever `G ≠ 0` |
| `differentiableAt_zetaLogDerivReg_one` | holomorphic *at* the pole |
| `zetaLogDerivReg_one` | its value there is `-γ` |

All `[propext, Classical.choice, Quot.sound]`.

The structural difference from the Möbius route is worth stating, because it is the whole content of
the Chebyshev route.  For `1/ζ` the crossing at `s = 1` contributed **nothing** — `invZeta 1 = 0` —
and the argument's conclusion was that the sum is small.  For `-ζ'/ζ` the crossing contributes the
residue `1`, and that residue *is* the main term `x` of `ψ(x) ~ x`.  So the same four-edge estimate,
applied to the same rectangle, produces a main term instead of `o(1)`, and the whole apparatus —
zero-free rectangle, edge bounds, balanced parameter, smoothing width — is reused unchanged.

What is genuinely new for this route: a bound for `zetaLogDerivReg` on the edges (the analogue of
`InvZetaLeftEdge`, and *not* implied by it, since `G'/G` and `1/ζ` are different functions), and the
residue computation that turns the crossing into `W(1)`.

#### The Perron formula's unit bound, examined — `RHTower/Sieve/PerronGeneralTerm.lean`

The Chebyshev route's coefficients are `Λ(n) ≤ log n`, which are **not** unit-bounded, and the
corpus's smoothed Perron formula `tsum_mul_smoothWeight_eq_integral` assumes `‖a n‖ ≤ 1`.  So the
first question for the route is how much of that hypothesis is real.

Examining where it is used gives a clean split.  It enters twice: in `integrable_perron_term` and in
the summability step of the main identity.  In the first it is **spurious** — that lemma is about a
*single* index `n`, so `‖a n‖` is a constant and any value of it is absorbed into the majorant.

`integrable_perron_term_general` — unconditional, `[propext, Classical.choice, Quot.sound]` — is the
same statement with no hypothesis on the coefficients at all.

What remains genuinely needed is the summability step: the identity equates the smoothed sum (a
*finite* sum, since the cutoff vanishes past `N+H`) with an integral of the *full* Dirichlet series,
so that series must converge on the line.  For `Λ` it does, for every `σ > 1`.  The right hypothesis
is therefore `Summable (fun n => ‖a n‖ * n^{-σ})` rather than a pointwise bound, and that is what a
`Λ`-usable Perron formula needs — a strictly weaker assumption than `‖a n‖ ≤ 1`, satisfied by every
Dirichlet series with abscissa of convergence below `σ`.

#### The Perron formula under absolute convergence — `RHTower/Sieve/PerronSummable.lean`

`tsum_mul_smoothWeight_eq_integral_summable` — unconditional,
`[propext, Classical.choice, Quot.sound]`: the smoothed Perron identity with `‖a n‖ ≤ 1` replaced by

    Summable (fun n => ‖a n‖ · n^{-σ}).

The unit bound was doing exactly one thing in the original proof: making the `L¹` norms of the terms
summable, via `∑ n^{-σ} < ∞`.  With the summability hypothesis that step is immediate and the
comparison disappears; nothing else in the proof changes.

The new hypothesis is the honest one.  The smoothed sum is finite — the cutoff vanishes past `N+H` —
but the identity equates it with an integral of the *full* Dirichlet series, so absolute convergence
on the line is genuinely required and a pointwise bound was only ever a sufficient condition for it.
Every Dirichlet series with abscissa of convergence below `σ` now qualifies, including `Λ` with its
`log n` growth, which is what the Chebyshev route needs.

So of the two obstructions to running the contour argument for `-ζ'/ζ`, both are now cleared: the
pole is split off (`ZetaLogDerivRegular`) and the Perron formula admits the coefficients
(`PerronSummable`).  What remains specific to that route is the edge bound for `zetaLogDerivReg` and
the residue computation at the crossing.

#### The Perron formula for `Λ` — `RHTower/Sieve/VonMangoldtPerron.lean`

| statement | content |
|---|---|
| `summable_norm_mul_rpow_of_LSeriesSummable` | `LSeriesSummable a σ` gives `Summable (‖a n‖·n^{-σ})` |
| `summable_vonMangoldt_rpow` | the instance for `Λ`, from mathlib's `LSeriesSummable_vonMangoldt` |
| `tsum_vonMangoldt_smoothWeight_eq_integral` | the smoothed Chebyshev sum as a vertical integral |
| `tsum_vonMangoldt_cpow_eq` | the integrand is `-ζ'/ζ` on `re s > 1` |

All `[propext, Classical.choice, Quot.sound]`.

The first is where mathlib does the work for us: `LSeriesSummable` is summability of the complex
terms, and over `ℕ` in a finite-dimensional space that is *absolute* (`summable_norm_iff`), which is
exactly the hypothesis `PerronSummable` asks for.  So no convergence estimate had to be proved for
`Λ` — mathlib's `LSeriesSummable_vonMangoldt` supplies it.

With these the Chebyshev route stands where the Möbius route stood at `MoebiusPerron`:

    2π · ∑ₙ Λ(n)·w(n)  =  ∫_ℝ (-ζ'/ζ)(d+iy) · W(d+iy) dy,      d > 1,

the identification of the integrand as `-ζ'/ζ` is done, and the pole at `s = 1` is already split off
by `ZetaLogDerivRegular`.  The remaining route-specific work is the edge bound for
`zetaLogDerivReg` and the residue at the crossing; everything else — zero-free rectangle, the four
edges, the balanced parameter, the smoothing width — is shared with the Möbius route and needs no
change.

#### The regular part shifts with no residue — `RHTower/Sieve/ZetaLogDerivRegShift.lean`

| statement | content |
|---|---|
| `differentiableOn_zetaLogDerivReg_rect` | `zetaLogDerivReg` is holomorphic on a zero-free rectangle |
| `differentiableOn_zetaLogDerivRegW_rect` | so is its product with the cutoff's transform |
| `integral_zetaLogDerivRegW_vertical_sub_eq_horizontal_rect` | the four-edge identity, no residue |
| `chebyshev_integrand_split` | `(-ζ'/ζ)·W = W/(s-1) + zetaLogDerivReg·W` |

All `[propext, Classical.choice, Quot.sound]`.

The holomorphy at the pole is the point: `zetaLogDerivReg` is `-G'/G` with `G(1) = 1 ≠ 0`, so it is
differentiable *at* `s = 1` and the rectangle argument needs no exception there — exactly as
`invZeta` was, and for the same reason.  The Cauchy identity for this part therefore carries no
residue at all.

So the entire residue of the Chebyshev integrand sits in the separated term `W(s)/(s-1)`.  That is
the formal content of "the main term of the prime number theorem is the pole of `ζ` and nothing
else": the analytic work of the contour argument — zero-free region, edge estimates, balanced
parameter — bears only on `zetaLogDerivReg`, and the main term comes from a single explicit rational
function.

What is left for this route: the residue computation for `∫ W(s)/(s-1)` around the rectangle (an
explicit Cauchy integral, no zeta input), and the edge bounds for `zetaLogDerivReg` (the analogue of
`InvZetaLeftEdge`, needing `‖G'/G‖` in place of `‖1/ζ‖`).

#### Splitting the pole term — `RHTower/Sieve/PoleTermSplit.lean`

| statement | content |
|---|---|
| `rect_mem_nhds_one` | a closed rectangle straddling `1` is a neighbourhood of it |
| `differentiableOn_dslope_mellin_rect` | `dslope W 1` is holomorphic on the rectangle |
| `mellin_div_sub_one_split` | `W(s)/(s-1) = dslope W 1 s + W(1)/(s-1)` off the pole |
| `integral_dslope_mellin_vertical_sub_eq_horizontal_rect` | the divided difference shifts with no residue |

All `[propext, Classical.choice, Quot.sound]`.

This isolates the residue completely.  The divided difference `dslope W 1` is holomorphic wherever
`W` is — including *at* `s = 1`, by mathlib's `Complex.differentiableOn_dslope`, whose only
hypothesis is that the domain be a neighbourhood of the point.  A closed rectangle whose abscissae
straddle `1` strictly is such a neighbourhood, which is what `rect_mem_nhds_one` supplies.

So the Chebyshev integrand is now three pieces, and only the last carries anything:

| piece | contour behaviour |
|---|---|
| `zetaLogDerivReg · W` | holomorphic on the zero-free rectangle — no residue |
| `dslope W 1` | holomorphic on the rectangle — no residue |
| `W(1)·(s-1)⁻¹` | the entire residue |

The last is an explicit rational function with no zeta content and no cutoff content beyond the
constant `W(1)`.  Mathlib has no rectangle residue formula — only the vanishing versions — so
`∫_{∂R}(s-1)⁻¹ = 2πi` is the one remaining computation, and it is a four-segment arctangent
evaluation independent of everything else in the route.

#### The vertical pole integral — `RHTower/Sieve/VerticalPoleIntegral.lean`

| statement | content |
|---|---|
| `integral_re_pole_line` | `∫_{-T}^{T} α/(α²+y²) dy = 2·arctan(T/α)` |
| `integral_im_pole_line` | `∫_{-T}^{T} -y/(α²+y²) dy = 0` — the integrand is odd |
| `tendsto_integral_re_pole_line` | that integral tends to `π` as `T → ∞` |

All `[propext, Classical.choice, Quot.sound]`.

These are the two halves of `(s-1)⁻¹` on a vertical line: real part `α/(α²+y²)` with `α` the distance
from the pole, imaginary part odd.  Half the residue comes from each side of the contour — `π` from
the right edge and `π` from the left — which is where the `2π` of `2πi` comes from.

The odd-part vanishing needs no hypothesis on `α` at all: the substitution `y ↦ -y` and
`intervalIntegral.integral_comp_neg` give it directly, and the sign of `α` never enters.  (I had
carried `0 < α` there and it was doing nothing.)

The arctangent computation reduces to mathlib's `integral_inv_one_add_sq` after the substitution
`y = αu`, which is `intervalIntegral.integral_comp_div`.  Nothing about `ζ` or the cutoff appears —
this is the piece of the prime number theorem that is pure real analysis.

#### The residue in real form — extending `VerticalPoleIntegral`

| statement | content |
|---|---|
| `inv_add_mul_I_eq` | `(α + iy)⁻¹ = α/(α²+y²) - i·y/(α²+y²)` |
| `tendsto_pole_difference` | the two vertical edges together tend to `2π` |

Both `[propext, Classical.choice, Quot.sound]`.

`tendsto_pole_difference` is the residue, stated in the form the contour argument produces it: the
right edge sits at distance `α = d - 1` from the pole and the left at `β = 1 - c`, each vertical
integral tends to `π`, and the two add — they do not cancel, because the contour traverses them in
opposite senses and the sign is already accounted for in the four-edge identity.

`inv_add_mul_I_eq` is proved by `inv_eq_of_mul_eq_one_right` and a real-part/imaginary-part check
rather than by `field_simp` on the complex expression, which does not close: `ring` has no access to
`I² = -1`, so the identity has to be reduced to two real ones first.  Worth remembering as the
general recipe for closed forms of complex reciprocals.

So the residue is now available in real form, and what remains for the Chebyshev route is to
assemble it with the horizontal edges and the two holomorphic pieces — the same assembly the Möbius
route already has, with `W(1)·2π` replacing `0` as the value of the crossing.

#### The complex vertical pole integral — completing `VerticalPoleIntegral`

`integral_vertical_pole` — unconditional, `[propext, Classical.choice, Quot.sound]`:

    ∫_{-T}^{T} ((α : ℂ) + iy)⁻¹ dy  =  2·arctan(T/α)      for α > 0,

a **real** number: the imaginary part cancels exactly.

The route that works is to substitute the closed form pointwise and then split with
`intervalIntegral.integral_sub` and `intervalIntegral.integral_ofReal`, rather than trying to
manipulate the complex integrand directly.  Both components are continuous — the denominator
`α² + y²` is bounded away from zero — so integrability is immediate and the split is unconditional.

With this the four pieces of the Chebyshev contour are all in hand:

| piece | value |
|---|---|
| `zetaLogDerivReg · W` | Cauchy identity, no residue |
| `dslope W 1` | Cauchy identity, no residue |
| right vertical of `W(1)(s-1)⁻¹` | `W(1)·2·arctan(T/(d-1))` |
| left vertical of `W(1)(s-1)⁻¹` | `W(1)·2·arctan(T/(1-c))` |

and the two arctangents sum to `2π` in the limit (`tendsto_pole_difference`).  The horizontal edges
of the pole term remain to be estimated — they are `O(1/T)` by the same argument as the other
horizontal edges, since `(s-1)⁻¹` is bounded by `1/T` at height `T`.

#### The horizontal edges of the pole term — `RHTower/Sieve/HorizontalPoleBound.lean`

| statement | content |
|---|---|
| `norm_inv_sub_one_le` | `‖(x + iT - 1)⁻¹‖ ≤ 1/\|T\|` |
| `norm_integral_horizontal_pole_le` | each horizontal edge is at most `(d-c)/\|T\|` |
| `tendsto_integral_horizontal_pole` | and vanishes as `T → ∞` |

All `[propext, Classical.choice, Quot.sound]`.

I said last time that this "should be `O(1/T)`" and would check rather than assume.  It is, and the
bound is exactly the trivial one: shifting by the real number `x - 1` leaves the imaginary part
alone, so `‖x + iT - 1‖ ≥ \|T\|` and the reciprocal is at most `1/\|T\|` uniformly in `x`.  No
cancellation is needed and no property of the abscissa range enters — unlike the earlier horizontal
edges, where the cutoff's transform carried an abscissa-dependent constant and that dependence was
where the route's one real defect hid.

All four edges of the pole term are now proved:

| edge | value |
|---|---|
| right vertical | `2·arctan(T/(d-1))` → `π` |
| left vertical | `2·arctan(T/(1-c))` → `π` |
| top horizontal | `≤ (d-c)/T` → `0` |
| bottom horizontal | `≤ (d-c)/T` → `0` |

so the boundary integral of `(s-1)⁻¹` tends to `2π` — the residue — with the two holomorphic pieces
contributing nothing.  Every ingredient of the Chebyshev contour identity is now an unconditional
theorem; what remains is to combine them, which is the same assembly the Möbius route already has.

#### Both vertical edges from one lemma — `integral_vertical_pole_pair`

`integral_vertical_pole_pair` — unconditional, `[propext, Classical.choice, Quot.sound]`: for
`c < 1 < d`,

    ∫_{-T}^{T}(d + iy - 1)⁻¹ dy - ∫_{-T}^{T}(c + iy - 1)⁻¹ dy
        = 2·arctan(T/(d-1)) + 2·arctan(T/(1-c)),

a real number tending to `2π`.

The generalisation that made this cheap: `integral_re_pole_line`, `inv_add_mul_I_eq` and
`integral_vertical_pole` were all stated with `0 < α`, but their proofs only ever use `α ≠ 0` — the
substitution `y = αu` and the closed form of the reciprocal are indifferent to the sign, and the
formula `2·arctan(T/α)` is *correct as stated* for negative `α`, where it is negative.  Weakening
the hypothesis lets the left edge, where `α = c - 1 < 0`, be handled by the same lemma as the right,
with the sign change appearing only in `arctan(T/(c-1)) = -arctan(T/(1-c))`.

Had I kept `0 < α` I would have needed a separate reflected computation for the left edge.  This is
the third time in this route that a hypothesis written for the first use turned out to be stronger
than the proof required.

The boundary integral of the pole term is now completely determined: two vertical edges summing to
`2π` in the limit, two horizontal edges each `O(1/T)`.

### The residue of the pole term — `RHTower/Sieve/PoleBoundaryResidue.lean`

`tendsto_pole_boundary` — unconditional, `[propext, Classical.choice, Quot.sound]`: for `c < 1 < d`,

    I•∫_{-T}^{T}(d+iy-1)⁻¹ - I•∫_{-T}^{T}(c+iy-1)⁻¹ - (∫_c^d(x+iT-1)⁻¹ - ∫_c^d(x-iT-1)⁻¹)  →  2πi.

| statement | content |
|---|---|
| `tendsto_two_arctan` | `2·arctan(T/α) → π` for `α > 0` |
| `tendsto_vertical_pole_pair` | the two vertical edges tend to `2π` |
| `norm_integral_horizontal_pole_neg_le` | the edge at height `-T` is also `≤ (d-c)/T` |
| `tendsto_horizontal_pole_pair` | both horizontal edges vanish |
| `tendsto_pole_boundary` | the residue |

All `[propext, Classical.choice, Quot.sound]`.

This is a residue theorem for the one function the route needs it for.  Mathlib has no rectangle
residue calculus — only the vanishing statements — so it is proved by direct computation: the
vertical edges by the arctangent evaluation, the horizontal ones by the trivial `1/T` bound.

The boundary functional here is *exactly* the one that
`integral_vertical_sub_eq_horizontal_rect` sets to zero for a holomorphic integrand.  So the
Chebyshev contour identity is now fully determined:

| integrand piece | boundary functional |
|---|---|
| `zetaLogDerivReg · W` | `0` (holomorphic on the zero-free rectangle) |
| `dslope W 1` | `0` (holomorphic on the rectangle) |
| `W(1)·(s-1)⁻¹` | `→ 2πi·W(1)` |

and `2πi·W(1)` is the main term of `ψ`, since `W(1) = ∫_0^∞ w(x) dx` is the mass of the cutoff — of
size `N` for a cutoff of width `N`.  That is the prime number theorem's `ψ(x) ~ x` in the smoothed
form, with the analytic work all pushed into `zetaLogDerivReg`.

#### The edge bound for the regular part — `RHTower/Sieve/ZetaLogDerivRegBound.lean`

| statement | content |
|---|---|
| `norm_zetaLogDerivReg_le` | `‖zetaLogDerivReg s‖ ≤ ‖ζ'(s)‖·‖1/ζ(s)‖ + ‖(s-1)⁻¹‖` |
| `norm_inv_sub_one_le_height` | `‖(β + iγ - 1)⁻¹‖ ≤ 1/\|γ\|` |
| `norm_zetaLogDerivReg_left_le` | the regular part on a line left of the abscissa |

All `[propext, Classical.choice, Quot.sound]`.

I expected this to be the one genuinely new analytic ingredient of the Chebyshev route, requiring a
bound on `G'/G` with `G = (s-1)ζ(s)` — a different function from `1/ζ`, so not implied by
`InvZetaLeftEdge`.  It is not: rearranging the splitting identity gives

    zetaLogDerivReg s = -ζ'(s)/ζ(s) - (s-1)⁻¹,

so the bound needs only `‖ζ'‖` and `‖1/ζ‖`, both already proved for the Möbius route, plus the
trivial `1/|γ|` for the pole term.  `G'` never has to be estimated.

`norm_zetaLogDerivReg_left_le` therefore reuses `norm_inv_riemannZeta_left_le_segment` verbatim, with
the same hypotheses, and adds `1/|γ|` — which at heights `|γ| ≥ 1` is at most `1` and so is
negligible beside the `log⁷N` of the main term.

So the Chebyshev route needs **no** new analytic input beyond what the Möbius route already
established.  Every ingredient — Perron formula, pole splitting, residue, edge bounds, zero-free
rectangle, balanced parameter, smoothing width — is now an unconditional theorem in the corpus.

#### The Chebyshev integrand in three pieces — `RHTower/Sieve/ChebyshevIntegrandSplit.lean`

| statement | content |
|---|---|
| `chebyshev_integrand_split_full` | `(-ζ'/ζ)·W = dslope W 1 + W(1)·(s-1)⁻¹ + zetaLogDerivReg·W` |
| `chebyshev_integrand_split_line` | the same on the Perron line, where the hypotheses are free |

Both `[propext, Classical.choice, Quot.sound]`.

The two splittings compose: the pole of `-ζ'/ζ` separates off `(s-1)⁻¹·W`, and the pole of that
separates off `W(1)·(s-1)⁻¹`, leaving `dslope W 1`.  The result is a three-term decomposition whose
contour behaviour is completely known:

| summand | zeta content | contour |
|---|---|---|
| `dslope W 1` | none | holomorphic on the rectangle — no residue |
| `W(1)·(s-1)⁻¹` | none | `→ 2πi·W(1)` |
| `zetaLogDerivReg · W` | all of it | holomorphic on a zero-free rectangle — no residue |

On the Perron line the two hypotheses `s ≠ 1` and `ζ(s) ≠ 0` are automatic, since `re s = d > 1`,
so `chebyshev_integrand_split_line` is unconditional in the parameters that matter.

Two of the three summands contain no zeta at all.  The main term of the prime number theorem comes
from the middle one, and the entire analytic difficulty is confined to the third — which the Möbius
route already bounded.

#### The four-edge combination with a residue — `RHTower/Sieve/ContourEdgesResidue.lean`

`norm_sub_le_of_contour_edges_residue` — unconditional,
`[propext, Classical.choice, Quot.sound]`: given the shift identity with a residue,

    I·Vd - I·Vc - (Ht - Hb) = Res,

and the four edge bounds, the Perron integral satisfies

    ‖P - (-I)·Res‖ ≤ E₁ + E₂ + E₃ + E₄.

This is the residue analogue of `norm_le_of_contour_edges`: where that bounds `‖P‖` when the
boundary functional vanishes, this bounds `‖P - main term‖` when it does not.  The proof is the same
triangle inequality with one extra step — solving the shift identity for `Vd - Vc` multiplies through
by `I⁻¹ = -I`, which is where the factor comes from and why the main term is `(-I)·Res` rather than
`Res`.

Applied to the Chebyshev route with `Res → 2πi·W(1)`, the main term is
`(-I)·2πi·W(1) = 2π·W(1)`, and the Perron identity carries a `2π` on the other side, so the
smoothed Chebyshev sum differs from `W(1)` — the mass of the cutoff — by the four edges.  That is
`ψ(x) ~ x` in smoothed form, with the constants matching without adjustment.

#### The mass of the cutoff — `RHTower/Sieve/CutoffMass.lean`

| statement | content |
|---|---|
| `mellin_smoothWeight_one` | `W(1) = ∫_0^∞ w(x) dx` |
| `integral_smoothWeight_le` | that mass is at most `N + H` |

Both `[propext, Classical.choice, Quot.sound]`.

`W(1)` is the residue's coefficient, so its size is the size of the prime number theorem's main term.
The transform at `s = 1` is just the integral of the cutoff, because the factor `x^{s-1}` becomes
`x^0 = 1`; and since `w ≤ 1` and vanishes past `N + H`, that integral is at most `N + H`.

With `w = 1` below `N` the mass is also at least `N`, so the main term is `N + O(H)` — which at the
smoothing widths this route uses (`H = N/L` with `L → ∞`) is `N(1 + o(1))`.  That is `ψ(x) ~ x`.

The integrability here is cleaner from continuity than from the corpus's Mellin machinery: the
cutoff is smooth and compactly supported in the relevant range, so `Continuous.integrableOn_Ioc`
plus a vanishing tail is enough, and the `x^{s-1}` weight never has to be carried.

#### The mass pinned from both sides — completing `CutoffMass`

| statement | content |
|---|---|
| `integrableOn_smoothWeight_Ioi` | the cutoff is integrable on `(0, ∞)` |
| `le_integral_smoothWeight` | `N ≤ W(1)` |

Both `[propext, Classical.choice, Quot.sound]`.  With `integral_smoothWeight_le` this gives

    N  ≤  W(1)  ≤  N + H,

so the main term of the smoothed Chebyshev sum is `N` up to the smoothing width.

The lower bound is the mirror of the upper: `w = 1` on `(0, N]` gives exactly `N` there, and the
remainder is nonnegative.  Splitting at `N` rather than at `N + H` is what makes it immediate —
the same `Ioc_union_Ioi_eq_Ioi` decomposition, at a different point.

Both bounds are stated for arbitrary `H > 0`, so they apply at the narrow smoothing widths the sharp
statement needs, where `H = N/L` and the gap between the two bounds is `N/L = o(N)`.

The main term of the Chebyshev route is therefore completely determined, and the route's remaining
work is the same numerical assembly the Möbius route already carries out.

#### The Chebyshev sharp/smooth comparison — `RHTower/Sieve/ChebyshevSmoothVsSharp.lean`

`norm_tsum_vonMangoldt_smoothWeight_sub_sum_le` — unconditional,
`[propext, Classical.choice, Quot.sound]`:

    ‖ ∑ₙ Λ(n)w(n) - ∑_{n ≤ N} Λ(n) ‖  ≤  (H + 1)·log(N + H)

for `N, H > 0` with `N + H ≥ 1`.

Same structure as the Möbius comparison, with one difference: the summand over the transition window
is bounded by `Λ(n) ≤ log n ≤ log(N+H)` rather than by `1`, so the cost is `(H+1)·log(N+H)` instead
of `H+1`.  That single logarithm is the only place the two routes' comparison steps differ.

The hypothesis `1 ≤ N + H` is not cosmetic and I nearly omitted it.  Without it the statement is
**false**: for `N + H < 1` the transition window contains no integers, so the left side is `0`, while
`log(N+H) < 0` makes the right side negative.  The bound only holds once the cutoff reaches the
integers it is supposed to weight.

The extra logarithm costs nothing at the smoothing widths this route uses: with `H = N/L` the
comparison is `N·log(2N)/L`, so it is `o(N)` as soon as `L/log N → ∞` — satisfied by
`L = exp((log N)^{1/20})` with enormous room.

#### The Chebyshev integrand on the Perron line — `RHTower/Sieve/ChebyshevRightLineBound.lean`

| statement | content |
|---|---|
| `norm_vonMangoldt_term` | `‖Λ(n)·n^{-s}‖ = Λ(n)·n^{-Re s}` |
| `norm_neg_logDeriv_le_line` | `‖(-ζ'/ζ)(d+iy)‖ ≤ ∑ₙ Λ(n)·n^{-d}` |
| `tsum_vonMangoldt_rpow_nonneg` | the bounding series is nonnegative |

All `[propext, Classical.choice, Quot.sound]`.

This is the uniform right-line bound the truncation error needs — the analogue of
`norm_LSeries_moebius_le_uniform`.  It is cheaper than the Möbius one, and for a structural reason:
the coefficients `Λ(n)` are **nonnegative**, so the triangle inequality gives the value of the same
series at the real point `d`, and no zero-free input is required at all.  The Möbius bound had to go
through the Euler product and `‖1/ζ‖`; here positivity does the work.

The bound is also sharp at `y = 0`, where it is an equality — so nothing is lost by using it.

With this the Chebyshev route has all four of its edge inputs:

| edge | bound |
|---|---|
| right line | `∑ Λ(n)n^{-d}` (this module) |
| horizontal | `zetaLogDerivReg` bound + pole term `O(1/T)` |
| left line | `norm_zetaLogDerivReg_left_le` |
| main term | `W(1) ∈ [N, N+H]` |

#### Continuity and truncation on the Perron line — `RHTower/Sieve/ChebyshevLineContinuity.lean`

| statement | content |
|---|---|
| `analyticAt_riemannZeta_of_ne_one` | `ζ` is analytic away from the pole |
| `continuous_neg_logDeriv_line` | `y ↦ (-ζ'/ζ)(d+iy)` is continuous for `d > 1` |
| `norm_truncation_error_chebyshev` | the truncation error, `≤ 2·(∑Λ(n)n^{-d})·C/T` |

All `[propext, Classical.choice, Quot.sound]`.

Analyticity is what makes the continuity immediate.  `differentiableAt_riemannZeta` alone says
nothing about `ζ'` being continuous; but a function complex-differentiable on an open set is
analytic there, and the derivative of an analytic function is analytic, hence continuous.  So the
quotient is continuous wherever `ζ` is nonvanishing and `s ≠ 1`.

`norm_truncation_error_chebyshev` is a direct instance of the Möbius route's
`norm_truncation_error_le` — the same lemma, with `-ζ'/ζ` in place of `invZeta` and the positivity
bound in place of the Euler-product one.  That the general lemma applies unchanged is the payoff of
having stated it for an arbitrary `F` with a bound and continuity on the line.

One practical note: the term-mode application timed out in `isDefEq`.  Supplying `F` explicitly —
`(F := fun s => -(deriv riemannZeta s) / riemannZeta s)` — fixes it, because the higher-order
unification of the integrand against `F (d + iy) * W (d + iy)` is what was searching.

#### The Chebyshev Perron identity — `RHTower/Sieve/ChebyshevPerronIdentity.lean`

| statement | content |
|---|---|
| `tsum_vonMangoldt_smoothWeight_eq_logDeriv_integral` | `2π ∑ₙ Λ(n)w(n) = ∫_ℝ (-ζ'/ζ)(d+iy)·W(d+iy) dy` |
| `tsum_vonMangoldt_smoothWeight_eq_split_integral` | the same with the integrand in its three pieces |

Both `[propext, Classical.choice, Quot.sound]`.

The second is the form the contour argument consumes: the smoothed Chebyshev sum is the integral of

    dslope W 1  +  W(1)·(s-1)⁻¹  +  zetaLogDerivReg·W

along the line `re s = d`.  Each summand's contour behaviour is already a theorem — the first and
third shift with no residue, the second contributes `2πi·W(1)` — so this identity is the last
structural step before the numerical assembly.

The Chebyshev route is now at parity with where the Möbius route stood at `PerronEdgeAssembly`, with
every route-specific ingredient proved:

| ingredient | module |
|---|---|
| Perron identity for `Λ` | `VonMangoldtPerron`, this module |
| pole split off | `ZetaLogDerivRegular`, `ZetaLogDerivRegShift` |
| pole term split further | `PoleTermSplit` |
| residue | `VerticalPoleIntegral`, `HorizontalPoleBound`, `PoleBoundaryResidue` |
| four-edge combination with residue | `ContourEdgesResidue` |
| main term size | `CutoffMass` |
| right-line bound and continuity | `ChebyshevRightLineBound`, `ChebyshevLineContinuity` |
| sharp/smooth comparison | `ChebyshevSmoothVsSharp` |
| edge bound for the regular part | `ZetaLogDerivRegBound` |

and the shared apparatus — zero-free rectangle, edge estimates, balanced parameter, smoothing
width — is reused from the Möbius route unchanged.

#### Splitting only after truncation — `RHTower/Sieve/ChebyshevTruncatedSplit.lean`

| statement | content |
|---|---|
| `dslope_mellin_line` | on a line right of the pole the divided difference is an explicit quotient |
| `sub_one_ne_zero_line` | the line stays away from the pole |
| `integral_truncated_chebyshev_split` | the truncated integral splits into the three pieces |

All `[propext, Classical.choice, Quot.sound]`.

The order matters, and getting it wrong would be a genuine error rather than an inefficiency.  The
three-piece decomposition **cannot** be integrated term by term over the whole line: the pole term
`W(1)·(s-1)⁻¹` decays like `1/|y|` there and is not integrable, even though the full integrand is.
So the argument must truncate first and split second — on `[-T, T]` every piece is continuous on a
compact interval and integrability is automatic.

That is why `norm_truncation_error_chebyshev` comes before this module in the chain, and not after.

Two Lean notes.  The divided difference is continuous on the line for the cheap reason: away from
`s = 1` it is `(W(s) - W(1))/(s-1)`, a quotient of continuous functions with nonvanishing
denominator — the removable-singularity theorem is only needed *at* the pole, which the line avoids.
And `intervalIntegral.integral_add` had to be applied with `f` and `g` given explicitly; the
rewrite fails otherwise, because the lemma's `(f + g) x` does not match a pointwise-written sum.

#### The main term, explicitly — `RHTower/Sieve/ChebyshevMainTerm.lean`

| statement | content |
|---|---|
| `integral_pole_term_line` | `∫_{-T}^{T} W(1)·((d+iy)-1)⁻¹ dy = W(1)·2·arctan(T/(d-1))` |
| `tendsto_integral_pole_term_line` | it tends to `π·W(1)` |

Both `[propext, Classical.choice, Quot.sound]`.

The middle piece of the split integrand is the only one contributing a main term, and on the
truncated Perron line it is *completely explicit* — a constant times an arctangent, with no
estimate anywhere.  That is unusual for an analytic number theory main term and worth stating:
the prime number theorem's `x` comes out of this route as an exact elementary integral, and every
inequality in the argument is spent on the error.

Combining with `CutoffMass`, the limit `π·W(1)` has `π·N ≤ π·W(1) ≤ π·(N+H)`, and the left edge
contributes the same again; the Perron identity's `2π` cancels both, leaving `W(1) ∈ [N, N+H]` as
the main term of `∑ₙ Λ(n)w(n)`.

Every piece of the Chebyshev contour identity is now proved and explicit.  What remains is the
numerical assembly — substituting the edge bounds and the balanced parameter, exactly as the Möbius
route does, with the difference that the conclusion is `ψ ~ N` rather than `o(N)`.

#### The truncated Chebyshev identity — `RHTower/Sieve/ChebyshevTruncatedIdentity.lean`

`tsum_vonMangoldt_truncated_identity` — unconditional,
`[propext, Classical.choice, Quot.sound]`:

    2π ∑ₙ Λ(n)w(n) = (tail beyond height T)
                     + ∫_{-T}^{T} dslope W 1
                     + W(1)·2·arctan(T/(d-1))
                     + ∫_{-T}^{T} zetaLogDerivReg·W

for `d > 1`.

This is an **identity**, not an estimate — the whole contour argument up to this point produces an
exact decomposition, with the main term already isolated in closed form.  Each of the four summands
then has its own treatment:

| summand | treatment |
|---|---|
| tail | `norm_truncation_error_chebyshev` |
| `∫ dslope W 1` | shifts to the left edge with no residue |
| `W(1)·2·arctan(T/(d-1))` | the main term, `→ π·W(1)` |
| `∫ zetaLogDerivReg·W` | shifts to the left edge with no residue |

The assembly of the identity was the step where the ordering constraint from the previous module
mattered: the split is applied to the *truncated* integral only, and the untruncated part appears
solely inside the tail bracket, where it is bounded rather than decomposed.

#### The smoothed sum against its main term — `RHTower/Sieve/ChebyshevMainTermBound.lean`

`norm_tsum_vonMangoldt_sub_main_le` — unconditional,
`[propext, Classical.choice, Quot.sound]`:

    ‖ 2π ∑ₙ Λ(n)w(n) - W(1)·2·arctan(T/(d-1)) ‖ ≤ E₁ + E₂ + E₃

given bounds `E₁`, `E₂`, `E₃` on the tail, the divided-difference integral and the regular integral.

This is the shape the numerical assembly consumes, and it is the Chebyshev analogue of
`norm_le_of_contour_edges`: the main term is explicit on the left, and the error is a sum of three
already-controlled quantities.  Only a triangle inequality separates it from the truncated identity,
because that identity is exact.

The Chebyshev route is now structurally complete.  Every step from the Riemann zeta function to

    ∑_{n ≤ N} Λ(n) = N + error

exists as an unconditional theorem: Perron identity, pole splitting, three-piece decomposition,
truncation, residue, main term in closed form, and the sharp/smooth comparison.  What is left is the
numerical work of substituting the edge bounds — the same substitution the Möbius route carries out
in `PerronSharpSubstitution` through `MoebiusSharpLittleO`, and reusing the same zero-free rectangle,
balanced parameter and smoothing width.

#### Chebyshev: the error on the shifted contour

Three further modules, all unconditional, all `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/ChebyshevErrorAssembly.lean` — `norm_tsum_vonMangoldt_sub_main_le_tail`.
  Substitutes `norm_truncation_error_chebyshev` for the first error piece, leaving
  `2·M·C/T + E₂ + E₃` with `M = ∑ₙ Λ(n)n^{-d}`.
- `RHTower/Sieve/ContourShiftNormBound.lean` — `norm_le_of_shift_identity`: a Cauchy identity
  `I·V_d - I·V_c = H_top - H_bot` gives `‖V_d‖ ≤ ‖V_c‖ + ‖H_top‖ + ‖H_bot‖`, since `I` is a unit.
  Instantiated at both residue-free pieces (`norm_integral_zetaLogDerivRegW_right_le`,
  `norm_integral_dslope_mellin_right_le`).
- `RHTower/Sieve/ChebyshevShiftedError.lean` — `norm_tsum_vonMangoldt_sub_main_le_shifted`:

      ‖ 2π ∑ₙ Λ(n)w(n) - W(1)·2·arctan(T/(d-1)) ‖
        ≤ 2·M·C/T
          + (left + top + bottom, divided difference)
          + (left + top + bottom, regular part)

  under `0 < c < 1 < d`, `1 ≤ T`, a zero-free rectangle and a Mellin decay constant.

The sign convention reconciled cleanly: both shift lemmas are stated as
`I • V_d - I • V_c = H_top - H_bot`, and the `I` costs nothing in norm, so no orientation
bookkeeping was needed — `norm_sub_le_of_contour_edges_residue` (which carries an explicit residue)
is not the right instrument here, because the residue was already extracted in closed form by
`integral_pole_term_line` before the shift.  That is the structural difference from the Möbius
route: there the residue is zero and the shift is the whole argument; here the residue is the main
term and the shift only handles what is left over.

Every quantity on the right is now an integral of an explicit integrand over an explicit edge, so
the remaining work is estimation only — the same six-edge substitution the Möbius route performs.

#### Correction: the divided difference is not small on the left edge

`norm_tsum_vonMangoldt_sub_main_le_shifted` is a true inequality, but its error term is **not**
small, so it cannot be the final assembly.  The reason is arithmetic in the residue:

    dslope W 1 (s) = W(s)/(s-1) - W(1)/(s-1),

and on `Re s = c < 1` the second summand integrates to `-W(1)·2·arctan(T/(c-1)) → +π·W(1)`.  That is
the same size as the main term `W(1)·2·arctan(T/(d-1)) → π·W(1)`, so bounding the left edge in norm
discards exactly half of the residue and the estimate becomes vacuous.

The residue theorem demands `2π·W(1)`, and the two lines supply `π·W(1)` each.  Three further
modules make that explicit, all unconditional, all `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/ChebyshevLeftPoleTerm.lean` — `integral_pole_term_line_of_ne` (the pole integral on
  *any* line off `1`, hypothesis weakened from `1 < a` to `a ≠ 1`) and
  `integral_dslope_mellin_left_eq`:

      ∫_{-T}^{T} dslope W 1 (c+iy) dy
        = ∫_{-T}^{T} W(c+iy)/(c-1+iy) dy - W(1)·2·arctan(T/(c-1)).

- `RHTower/Sieve/ChebyshevFullMainTerm.lean` — `eq_of_shift_identity` (solve a residue-free shift for
  the right edge: `V_d = V_c - I·(H_top - H_bot)`) and `tsum_vonMangoldt_full_main_identity`:

      2π ∑ₙ Λ(n)w(n) - W(1)·(2·arctan(T/(d-1)) - 2·arctan(T/(c-1)))
        = tail + (∫ W(c+iy)/(c-1+iy) dy - I·(top - bottom)) + ∫ regular.

- `RHTower/Sieve/ChebyshevFullBound.lean` — `tendsto_two_arctan_neg`, `tendsto_main_bracket`
  (the bracket `→ 2π`), and `norm_tsum_vonMangoldt_sub_full_main_le`, the six-edge estimate with the
  full main term and the pole-free left edge.

Dividing by `2π`, this is `∑ₙ Λ(n)w(n) = W(1) + error` with `W(1)` the mass of the cutoff, which
`CutoffMass` places between `N` and `N + H`.

The lesson generalises beyond this card: a holomorphic splitting that shifts *without* a residue is
not automatically a splitting that is *small* after the shift.  `dslope` is holomorphic everywhere
`W` is, so the shift is free — but the object it is holomorphic across still carries the pole's mass
on the far line.  Isolating the residue analytically and isolating it quantitatively are two
different steps.

#### Every edge bounded — `norm_tsum_vonMangoldt_sub_full_main_le_explicit`

Four further modules, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/ChebyshevLeftVerticalBound.lean` — `norm_inv_sub_one_line_le` (the pole factor is
  `≤ (1-c)⁻¹` on a line left of `1`, from `|Re| ≤ ‖·‖`) and
  `norm_integral_left_vertical_pole_free_le`:
  `‖∫ W(c+iy)/(c-1+iy) dy‖ ≤ (1-c)⁻¹·(2(N+H)^c/c + 2C_c)`.
- `RHTower/Sieve/ChebyshevHorizontalDslope.lean` — `norm_dslope_mellin_height_le`,
  `norm_integral_horizontal_dslope_le`: each horizontal edge of the divided difference is
  `≤ (d-c)·(C_d/T² + ‖W(1)‖)/|T|`.
- `RHTower/Sieve/ChebyshevRegularEdges.lean` — `continuousOn_zetaLogDerivReg_line`,
  `norm_integral_horizontal_reg_le` (`≤ (d-c)·R·C_d/T²`) and `norm_integral_left_vertical_reg_le`
  (`≤ M·(2(N+H)^c/c + 2C_c)`).
- `RHTower/Sieve/ChebyshevExplicitBound.lean` — `norm_tsum_vonMangoldt_sub_full_main_le_explicit`,
  the six edges substituted.

Two decay constants are carried separately by design: `C_c` on the line `Re s = c`, `C_d` on the
strip `0 < Re s ≤ d`.  Merging them reintroduces the abscissa-range trap — a strip constant carries a
factor `(N+H)^d`, which exceeds the saving the contour buys.

**The horizontal edges are not small in absolute terms, and that is fine.**  Each carries
`(d-c)·‖W(1)‖/T`, of the same order as `N/T` — but the main term is `2π·W(1)`, so the *ratio* is
`(d-c)/(2πT)`, which vanishes with the truncation height.  This is the counterpart of the left-edge
correction above: there the mass had to be extracted because it was comparable to the main term, here
it may be kept because the height divides it away.  A residue-theorem treatment of the whole
integrand would avoid these terms entirely, at the cost of a rectangle residue computation
(`∮ (s-1)⁻¹ ds = 2πi` via `Complex.log` on the horizontal segments); the arctan bookkeeping used here
reaches the same estimate without it.

With `d = 1 + 1/log N`, `T = exp((log N)^{1/10})` and `c = 1 - c₀/log⁹T`, every term on the right is
`o(N)` while the left-hand main term is `2π·W(1) ≍ N` — so the estimate is
`∑ₙ Λ(n)w(n) = W(1) + o(N)`, and `CutoffMass` places `W(1)` between `N` and `N+H`.

#### The regular part is bounded on the whole contour box

Three modules, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/ZetaLogDerivRegStrip.lean` — `riemannZeta_ne_zero_strip` (immediate from the
  quartic lower bound `pow_four_norm_riemannZeta_ge_strip`) and `norm_zetaLogDerivReg_strip_le`:
  for `|t| ≥ 9` and `|σ-1| ≤ A/log⁹|t|`,

      ‖zetaLogDerivReg(σ+it)‖ ≤ (2240/A)·log⁹|t| + 1/9.

  The corpus already owned `norm_deriv_div_riemannZeta_le` (`‖ζ'/ζ‖ ≤ (2240/A)log⁹|t|` on the
  strip); the regular part differs from `-ζ'/ζ` only by the pole, at distance `|t| ≥ 9`.
- `RHTower/Sieve/ZetaLogDerivRegLowBox.lean` — `exists_bound_zetaLogDerivReg_low_box`: below height
  `9`, compactness plus holomorphy on a zero-free box (the pole costs nothing, `zetaLogDerivReg 1`
  being `-γ`).
- `RHTower/Sieve/ZetaLogDerivRegBox.lean` — `strip_width_mono`, `riemannZeta_ne_zero_box`,
  `norm_zetaLogDerivReg_box_le` and `exists_low_data`.

The key geometric point is `strip_width_mono`: the zero-free strip is *wider* at lower height, so a
rectangle whose half-width is fixed at the truncation height's value, `A/log⁹T`, sits inside the
strip at every height it meets.  This also fixes the right abscissa: `d = 1 + A/log⁹T` rather than
anything larger, so the top and bottom edges stay inside the strip too.  The Dirichlet-series
constant that choice costs is `1/(d-1) = log⁹T/A`, only polylogarithmic.

With this, all three zeta-analytic inputs of `norm_tsum_vonMangoldt_sub_full_main_le_explicit` —
`hzfrect`, `hregline`, `hregtop`/`hregbot` — are discharged by a single box statement, with
`R = M = max M₀ ((2240/A)log⁹T + 1/9)`.

#### The contour fixed, the data supplied

Two more modules, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/ChebyshevBoxSubstitution.lean` — `norm_tsum_vonMangoldt_sub_full_main_le_box`:
  the explicit six-edge estimate with `c = 1 - A/log⁹T`, `d = 1 + A/log⁹T`, and every zeta-analytic
  hypothesis discharged from the box lemmas.  The main term becomes

      W(1)·(2·arctan(T·log⁹T/A) - 2·arctan(-T·log⁹T/A)),

  which is the bracket `→ 2π`.
- `RHTower/Sieve/ChebyshevContourData.lean` — `exists_height_fit` and
  `exists_chebyshev_contour_data`: a single `(δ₀, M₀)` serving the zero-free box and the regular-part
  bound below height `9`, plus a threshold `T₀` beyond which `A/log⁹T ≤ δ₀`.  None of these
  constants depends on the cutoff, so they are fixed once and reused at every `N`.

What is left in the bound after this is the cutoff's Mellin transform (decay constants `C_c`, `C_d`
from `exists_bound_mellin_smoothWeight_upto`, of sizes `(N+H+1)^{1∓A/log⁹T}`) and the contour
parameters — no further information about `ζ` appears anywhere.

#### The balanced height and its two exponent estimates

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/ChebyshevHeight.lean` — `chebHeight x = exp((log x)^{1/10})`, with
  `log_chebHeight`, `log_chebHeight_pow_nine` (`log⁹T = (log x)^{9/10}`, so the strip half-width is
  `w = A/(log x)^{9/10}`), `nine_le_chebHeight` and `tendsto_chebHeight`.
- `RHTower/Sieve/ChebyshevSaving.lean` — `div_rpow_nine_tenths` (`u/u^{9/10} = u^{1/10}`),
  `rpow_left_le_saving` (`Y^{1-w} ≤ Y·exp(-A(log x)^{1/10})` for `Y ≥ x`) and
  `rpow_right_le_growth` (`Y^{1+w} ≤ Y·exp(w·log Y)`).

The exponent `1/10` is forced by the ninth power in the zero-free region: the saving on the left edge
is `exp(-A(log x)^{1/10})` and the truncation height is `exp((log x)^{1/10})`, so the tail's growth
`exp(A(log x)^{1/10})` is divided away exactly because `A ≤ 1/2 < 1`.  A smaller exponent weakens the
left edge, a larger one overwhelms the right edge — both sides are tight at `1/10`.

#### The last prime-side quantity removed

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/ChebyshevSeriesBound.lean` — `tsum_vonMangoldt_rpow_neg_le`:
  `∑ₙ Λ(n)n^{-d} ≤ 8/(d-1)²` for `1 < d ≤ 2`.  The corpus already owned this as
  `RHTower.tsum_vonMangoldt_div_rpow_le`; only the termwise form differed (`Λ(n)/n^d` against
  `Λ(n)·n^{-d}`), and the two agree everywhere including `n = 0`.
- `RHTower/Sieve/ChebyshevBoxTail.lean` — `norm_tsum_vonMangoldt_sub_full_main_le_box_tail`: the box
  estimate with `8/w²` in place of the series.

After this substitution **no quantity in the bound refers to the primes or to `ζ`**.  Every term is
built from the cutoff's Mellin transform, the strip half-width `w = A/log⁹T`, the truncation height
`T`, and the two absolute constants `M₀`, `A`.  What is left is arithmetic on those.

#### The width, and the one inequality that makes the parameters compatible

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/ChebyshevWidth.lean` — `chebWidth x = x/exp((log x)^{1/20})`, with
  `chebWidth_pos`, `chebWidth_le`, `div_chebWidth` (`x/H = exp((log x)^{1/20})`) and
  `sqrt_logRoot`: `√((log x)^{1/10}) = (log x)^{1/20}`.
- `RHTower/Sieve/SqrtExpDecay.lean` — `tendsto_poly_sqrt_exp_neg`:
  `t^n·exp(2√t)·exp(-κt) → 0` for every `κ > 0`, because `2√t ≤ κt/2` once `t ≥ (4/κ)²`.

These two are what make the three parameters compatible.  The decay constant of the cutoff's
transform carries `(x/H)² = exp(2√t)`; the contour's saving is `exp(-At)`; and `√t` against `t` is
the only reason the first does not eat the second.  Writing the width's exponent as `1/20` — exactly
half of the height's `1/10` — is not a convenience: any exponent `≥ 1/10` would make `(x/H)²`
overwhelm the saving, and any smaller one would make the sharp-versus-smooth error `H·log x` too
large.

The sharp-versus-smooth error at this width is `x·(log x)/exp(√t) = x·t^{10}·exp(-√t)`, which is
`o(x)`, so the smoothing is invisible in the final statement.

#### The two decay constants at the balanced parameters

`RHTower/Sieve/ChebyshevDecayAtChoice.lean`, unconditional,
`[propext, Classical.choice, Quot.sound]`:

- `add_chebWidth_le` — `N + H + 1 ≤ 3N`.
- `decay_coeff_le` — `C/H²·(N+H+1)² ≤ 9C·exp(2(log N)^{1/20})`.
- `decay_left_le` — `C_c ≤ 27C·N·exp(2(log N)^{1/20})·exp(-A(log N)^{1/10})`.
- `decay_right_le` — `C_d ≤ 81C·N·exp(2(log N)^{1/20})·exp(A(log N)^{1/10})`.

The constant `C` is absolute: `exists_bound_mellin_smoothWeight_uniform_all` in the corpus already
exposes the cutoff dependence as the explicit factor `H^{-(j+1)}(N+H+1)^{j+1}`, with a constant
depending only on the order.  That is what makes the substitution possible at all — an existential
constant depending on `N` and `H` could not be tracked through the limit.

Both constants are `N` times a function of `t = (log N)^{1/10}` alone.  The left one already carries
the contour's saving `exp(-At)`; the right one carries the matching growth `exp(At)`, which the
truncation height `exp(t)` divides away because `A ≤ 1/2 < 1`.

#### The estimate at the balanced parameters

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/ChebyshevLimitTool.lean` — `tendsto_logRoot` and `tendsto_logPoly_sqrt_saving`:

      t^n · exp(2(log x)^{1/20}) · exp(-κ(log x)^{1/10}) → 0,   t = (log x)^{1/10}, κ > 0.

  Every error term of the contour bound, divided by the cutoff, is a constant times an instance of
  this — so this single limit is what the whole numerical assembly reduces to.
- `RHTower/Sieve/ChebyshevAtChoice.lean` — `norm_tsum_vonMangoldt_sub_main_at_choice`: the box
  estimate with `T = chebHeight N` and `H = chebWidth N` substituted, the strip half-width rewritten
  as `A/(log N)^{9/10}`, and the two decay constants written out explicitly in `N`.

The statement is now entirely in `N`: the only remaining quantities are `Cj` (absolute), `M₀`
(absolute), `A = zetaLowerA` (absolute) and elementary functions of `log N`.

#### The three ingredients of the numerical bound

Three modules, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/ChebyshevMassBound.lean` — `norm_mellin_smoothWeight_one_le`: `‖W(1)‖ ≤ N + H`.
- `RHTower/Sieve/ChebyshevSavingFactors.lean` — the two decaying factors

      E(x) = exp(2(log x)^{1/20})·exp(-A t),   G(x) = exp(2(log x)^{1/20})·exp(-(1-A)t),

  with `tendsto_pow_savingE`, `tendsto_pow_savingG` (any power of `t` against either tends to `0`),
  `zetaLowerA_le_half`, `rpow_nine_tenths_eq` and `one_le_logRoot`.
- `RHTower/Sieve/ChebyshevTermBounds.lean` — `decay_right_div_height_le` (the right-edge decay
  constant divided by *any* positive power of the height is `≤ 81C·N·G`), `bracket_le` (the bracket
  shared by the two left-edge terms is `≤ (8 + 54C)·N·E`) and `regBound_le`
  (`max M₀ (2240t⁹/A + 1/9) ≤ M₀ + 2240t⁹/A + 1/9`).

`A ≤ 1/2` enters exactly once, in `tendsto_pow_savingG`: it is what makes `1 - A > 0`, i.e. what
makes the truncation height `exp(t)` beat the right-edge decay constant's growth `exp(At)`.  Every
other use of the zero-free constant is qualitative.

#### The smoothed Chebyshev error is `o(N)` — unconditional

Two modules close the numerical assembly, both `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/ChebyshevFiveTerms.lean` — `term_tail_le`, `term_left_dslope_le`,
  `term_horizontal_dslope_le`, `term_left_reg_le`, `term_horizontal_reg_le`: each of the five error
  terms bounded by a constant times `t^k·N·E` or `t^k·N·G` with `k ∈ {0, 9, 18}`.
- `RHTower/Sieve/ChebyshevErrorLimit.lean` — `norm_tsum_vonMangoldt_sub_main_five_terms`,
  `tendsto_five_term_majorant`, and

      tendsto_norm_tsum_vonMangoldt_sub_main_div :
        ‖ 2π ∑ₙ Λ(n)w(n) - W(1)·(2·arctan(T/w) - 2·arctan(-T/w)) ‖ / N  →  0.

All the existential data is discharged inside: `C` from `exists_bound_mellin_smoothWeight_uniform_upto`,
and `(T₀, δ₀, M₀)` from `exists_chebyshev_contour_data`.  The statement has **no hypotheses**.

The powers of `t` that appear are exactly the three places the strip's width enters: `w⁻¹ = t⁹/A` in
the two left-edge terms, `w⁻² = t¹⁸/A²` in the truncation error, and the regular part's own bound
`2240t⁹/A`.  Nothing of higher order occurs, which is why the exponent `1/10` suffices.

Remaining to reach `ψ(N) ~ N`: the bracket tends to `2π` (because `T/w = t⁹exp(t)/A → ∞`), the mass
`W(1)` lies between `N` and `N+H` with `H/N → 0`, and the sharp-versus-smooth error is
`(H+1)log(N+H) = o(N)`.

### The prime number theorem, unconditional in Lean

`RHTower/Sieve/ChebyshevMainTermLimit.lean` and `RHTower/Sieve/ChebyshevPNT.lean` close the chain.
All statements are unconditional with axioms `[propext, Classical.choice, Quot.sound]`:

- `tendsto_chebWidth_div` — `H/N = exp(-(log N)^{1/20}) → 0`.
- `tendsto_mass_div` — `W(1)/N → 1` (the mass lies between `N` and `N + H`).
- `tendsto_height_div_width`, `tendsto_bracket_at_choice` — the bracket is `4·arctan(T/w)` and
  tends to `2π`, because `T/w = t⁹exp(t)/A → ∞`.
- `tendsto_width_mul_log`, `tendsto_window_mass_div` — the smoothing error
  `(H+1)log(N+H)/N → 0`; the key identity is `(log N)^{1/20}` raised to the 20th power being
  `log N`, so the width's exponential beats the logarithm.
- `tendsto_tsum_vonMangoldt_smoothWeight_div` — `∑ₙ Λ(n)w(n)/N → 1`.
- `tendsto_smooth_sub_sharp_div` — smoothed minus sharp is `o(N)`.
- **`tendsto_sum_vonMangoldt_div`** —

      ψ(x)/x → 1,   i.e.   Tendsto (fun x => (∑_{n ≤ x} Λ(n))/x) atTop (𝓝 1).

  **No hypotheses.**  This is the prime number theorem.

The corpus now owns both classical forms of PNT unconditionally: `∑_{n≤N} μ(n) = o(N)`
(`tendsto_norm_sum_moebius_div`, proved earlier on this card) and `ψ(x) ~ x`.  mathlib v4.32.2 has
neither.

Route from `riemannZeta` to `ψ(x) ~ x`, end to end: smoothed Perron identity → removable singularity
at `s = 1` (`zetaLogDerivReg`) → truncation → three-piece split → residue in closed form (arctan) →
contour shift on the zero-free box `|σ-1| ≤ A/log⁹T`, `|t| ≤ T` → six edge estimates → balanced
parameters `T = exp((log N)^{1/10})`, `H = N/exp((log N)^{1/20})` → five decaying terms → limit.

The three exponents are forced and mutually tight: `9` by the zero-free region, `1/10` because the
saving `exp(-A(log N)^{1/10})` must survive the truncation height `exp((log N)^{1/10})` (possible
only because `A ≤ 1/2 < 1`), and `1/20` because `(N/H)² = exp(2(log N)^{1/20})` must be beaten by
that same saving while `H·log N` stays `o(N)`.

### Step 1's two non-MR inputs are now formalized

Both analytic inputs the bilinear all-interval theorem `(5)` is applied to are proved
unconditionally, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/MoebiusDyadicWindow.lean` — `tendsto_norm_window_sum_moebius_div` and
  `tendsto_norm_sum_moebius_Ioc_div`:

      (1/y) ‖∑_{y < n ≤ 2y} μ(n)‖ → 0.

  This is the card's "the prime number theorem gives `(1/√x)∑_{√x ≤ n ≤ 2√x} μ(n) = o(1)`", at
  `y = √x`.  It is a two-line consequence of `tendsto_norm_sum_moebius_div` once that is available:
  a dyadic block is a difference of two initial segments, and both are `o` of the scale.

- `RHTower/Sieve/SquarefreeWindowCount.lean` and `RHTower/Sieve/SquarefreeDyadicDensity.lean` —
  `filter_sq_dvd_high_eq_empty`, `abs_window_squarefree_sub_le`, `tendsto_window_squarefree_density`:

      | #{n ∈ (t, t+L] : n squarefree} - L·D | ≤ R + L/R   (for 1 ≤ R, t+L ≤ R²),
      (1/y) ∑_{y < n ≤ 2y} μ²(n) → D = 6/π².

  This is the card's "squarefree density gives `(1/√x)∑_{√x ≤ n ≤ 2√x} μ²(n) = D + o(1)`".

The truncation defect vanishes identically once `R² ≥ t + L`: a divisor `d > R` has `d² > R² ≥ n`,
while `d² ∣ n` with `n ≥ 1` forces `d² ≤ n`.  So no averaged tail estimate is needed at all — the
corpus's `AveragedSquarefreeTail` layer is only required when `R` is taken *below* the square root,
which the dyadic window never needs.  Choosing `R = ⌊√(t+L)⌋ + 1` gives the error `O(√(t+L))`.

Step 1 of the card therefore now rests on `(5)` alone.

### Step 2's density input `(8)` is now formalized analytically

`MobiusCoprimeEulerMargin.euler_exclusion_factor` had only the Euler-factor *ratio*
`(1-1/p)/(1-1/p²) = p/(p+1)`.  The analytic content of `(8)` — that this ratio is the actual limiting
density — is now proved, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/CoprimeMoebiusSeries.lean` — `coprimeMoebiusTerm`, `coprimeSquarefreeSum`,
  `summable_coprimeMoebiusTerm`, `abs_sum_Icc_coprimeMoebius_sub_le`, `moebius_prime_mul`,
  `tsum_deleted_eq`, and

      coprimeSquarefreeSum_mul_eq :  S_p · (1 - p^{-2}) = D,   S_p = ∑_{p ∤ d} μ(d)/d².

  The proof is the reindexing `d = p·e` of the deleted part: `μ(pe) = 0` when `p ∣ e` and `-μ(e)`
  otherwise, so the deleted part is exactly `-p^{-2}·S_p`.
- `RHTower/Sieve/CoprimeSquarefreeWindow.lean` — `filter_sq_dvd_Icc_eq`, `moebius_sq_eq_sum_trunc`,
  `sq_dvd_and_prime_dvd_iff`, `card_filter_coprime_eq`, `abs_count_coprime_sub_le`,
  `filter_coprime_eq_empty_of_dvd`, and

      abs_window_coprime_squarefree_sub_le :
        | #{n ∈ (t,t+L] : squarefree, p ∤ n} - L·(1-1/p)·S_p | ≤ 2R + L/R.

  The sieve is the same as the unrestricted one with each inner count `#{d² ∣ n}` replaced by
  `#{d² ∣ n} - #{p d² ∣ n}` — legitimate exactly because `p ∤ d` makes `p` and `d²` coprime, so
  `d² ∣ n ∧ p ∣ n ↔ p d² ∣ n`.  Divisors `d` with `p ∣ d` contribute nothing on either side.
- `RHTower/Sieve/CoprimeSquarefreeDyadic.lean` — `coprime_density_eq`
  (`(1-1/p)·S_p = D·p/(p+1)`) and

      tendsto_window_coprime_squarefree_density :
        (1/y) ∑_{y < m ≤ 2y} μ²(m)·1_{p ∤ m} → D·p/(p+1).

This is precisely the card's `(8)`.  All three of the card's analytic density inputs — the Möbius
mean, the squarefree density, and the `p`-deleted squarefree density — are now unconditional Lean
theorems.  The card's remaining dependence is on Matomäki–Radziwiłł's Theorem 2 alone.

### Step 3's tail estimate `(11)` is now formalized

`RHTower/Sieve/SharedPrimeTailLimit.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `mertensS_sqrt_le` — `mertensS(⌊2√x⌋) ≤ log log(3x) + C` (Mertens' second theorem at the balanced
  height; the corpus already owned `mertensS_le`).
- `shared_prime_tail_normalized_le` — dividing the corpus's `sum_pair_tail_le` by `h·√x`:

      (tail over primes > P)/(h√x) ≤ 1/P + [ (√x + h)·mertensS(2√x) + 2√x ] / (h√x).

- `excess_eq` — the bracket is exactly `mertensS/h + mertensS/√x + 2/h`.
- `tendsto_of_growth` — the card's condition `(1)` forces `h → ∞`.
- `tendsto_loglog_div_sqrt` — `log log(3x)/√x → 0`.
- `tendsto_shared_prime_excess` — the bracket tends to `0`.
- `eventually_shared_prime_tail_le`, **`exists_shared_prime_tail_small`** — the card's `(11)`:

      ∀ ε > 0, ∃ P ≥ 1, eventually  (tail over primes > P)/(h√x) ≤ ε.

The three pieces of the bracket are governed by exactly one hypothesis each: the first by the card's
growth condition `h/log log(3x) → ∞` (it *is* its reciprocal), the second by `log log(3x) = o(√x)`,
the third by `h → ∞`.  Nothing else about `h` is used, and the estimate is uniform in the interval
data — no distribution theorem enters, as the module's original design intended.

#### Status of the card's numbered equations

| eq | content | Lean |
|----|---------|------|
| (5) | Matomäki–Radziwiłł Theorem 2 | **external — the sole gate** |
| (6),(7) | densities → signed/absolute pair counts | needs (5) |
| (8) | `p`-deleted squarefree density `D·p/(p+1)` | **done** (`CoprimeSquarefreeDyadic`) |
| (9) | shared-prime sector density | algebraic form done; analytic form needs (5) |
| (10),(11) | uniform large-prime tail | **done** (`SharedPrimeTail`, `SharedPrimeTailLimit`) |
| (12) | noncoprime pairs `≤ D²A` | needs (9), hence (5) |
| (13) | `A ≤ 13/36 < 1/2` | **done** (`MobiusCoprimeEulerMargin`) |
| step 1 inputs | `∑μ = o`, `∑μ² ~ D` over `[√x, 2√x]` | **done** |

Every line of the card that does not pass through `(5)` is now an unconditional Lean theorem.

### The sign split `(7)` is now an exact Finset identity

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/SignSplitLimit.lean` — `tendsto_pos_class`, `tendsto_neg_class`,
  `tendsto_sign_classes`: from `R₊+R₋ = Q`, `R₊-R₋ = S`, `Q/N → q`, `S/N → 0` conclude
  `R±/N → q/2`.  Also `le_liminf_after_deletion`, the card's step-4 bookkeeping (deleting a set of
  density `b` from a class of density `q` leaves `≥ q - b - ε` eventually).
- `RHTower/Sieve/BalancedPairs.lean` — `balancedPairs x h` (the pair set
  `x ≤ n₁n₂ ≤ x+h√x`, `√x ≤ n₁ ≤ 2√x`), `signedPairSum`, `squarefreePairCount`, `signClass`,
  `signClassCount`, and the two **exact** identities

      ∑ μ(n₁)μ(n₂) = R₊ - R₋,     ∑ μ²(n₁)μ²(n₂) = R₊ + R₋,

  valid for every `x` and `h` with no hypotheses at all, together with
  `tendsto_signClass_of_limits`, the card's `(7)`.

The identities hold because `μ(n₁)μ(n₂)` and `μ²(n₁)μ²(n₂)` are the difference and the sum of the
two sign indicators — a three-case check, no arithmetic.  So `(7)` is *not* an analytic step: the
only analytic content is the two limits, i.e. `(5)` applied to `μ` and to `μ²`.

The card's logical skeleton is now fully in Lean except for `(5)` itself: every arrow between
numbered equations that does not start at `(5)` is a machine-checked theorem.

### The card's `(5)` is now an explicit Lean interface, and `(7)` is derived from it

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/BlockMean.lean` — `blockMean f x = (1/√x)∑_{√x < n ≤ 2√x} f(n)`, with
  `tendsto_blockMean_moebius` (`→ 0`) and `tendsto_blockMean_moebius_sq` (`→ D`).  Both are the
  dyadic-window limits of the previous section composed with `x ↦ √x`; the block was *defined* as
  `(√x, 2√x]` precisely so that they apply verbatim.
- `RHTower/Sieve/MRInterface.lean` — `pairSum f x h`, and the card's `(5)` as a `Prop`:

      MRBilinear f hh :=
        Tendsto (fun x => pairSum f x (hh x)/(hh x·√x·log 2) - (blockMean f x)²) atTop (𝓝 0)

  together with `tendsto_signedPairSum_of_MR`, `tendsto_squarefreePairCount_of_MR` and

      tendsto_signClass_of_MR :
        MRBilinear μ hh → MRBilinear μ² hh →
          signClassCount(±1)/(h√x log 2) → D²/2.

  This is the card's `(7)`, machine-checked, with `(5)` as its only hypothesis.

Two facts fall out of the interface being definitional rather than axiomatic:
`signedPairSum = pairSum μ` and `squarefreePairCount = pairSum μ²` hold by `rfl` — the two
applications of `(5)` the card makes are literally the same statement at two weights, and the sign
split needs nothing else.

Following `formal/CLAUDE.md`'s rule for missing analytic inputs (explicit hypotheses or `Prop`
interfaces), the card's dependence on Matomäki–Radziwiłł is now a single named `Prop` rather than a
prose remark, and every downstream step is checked against it.

### Step 2's rescaling is now an exact Finset bijection

`RHTower/Sieve/BalancedPairsRescale.lean`, unconditional,
`[propext, Classical.choice, Quot.sound]`:

- `mem_balancedPairs` — for `x > 0` the bounding box in the definition of `balancedPairs` is
  *implied* by the product constraint, so membership is exactly the four real inequalities.  (If
  `x ≤ n₁n₂` and `x > 0` then both entries are `≥ 1`, hence each is `≤ n₁n₂ ≤ x + h√x`.)
- `sqrt_div_sq`, `rescaled_endpoint` — `√(x/p²) = √x/p` and
  `x/p² + (h/p)·√(x/p²) = (x + h√x)/p²`.
- **`balancedPairs_shared_eq_image`** —

      { balanced pairs with p ∣ n₁ and p ∣ n₂ }  =  image (m₁,m₂) ↦ (p m₁, p m₂)
        of  balancedPairs (x/p²) (h/p).

  An exact Finset identity: the four constraints transform into each other by the two displays
  above, so the card's `X_p = x/p²`, `h_p = h/p` is not an approximation but a bijection.
- `coprimeSquarefreeWeight p n = μ²(n)·1_{p∤n}`, `moebius_sq_prime_mul` (`μ²(pa) = f_p(a)` for `p`
  prime), and

      sharedSectorCount_eq_pairSum :
        C_p(x,h) = pairSum (coprimeSquarefreeWeight p) (x/p²) (h/p).

So the card's `(9)` is now *definitionally* an instance of `(5)` at the weight `f_p` and the
parameters `(X_p, h_p)`; combined with `tendsto_window_coprime_squarefree_density` (the `(8)` limit
proved earlier) it yields `C_p/(h√x log 2) → D²/(p+1)²` as soon as the interface is available there.
The `1/p²` of `(9)` is exactly the Jacobian `h_p√X_p = h√x/p²` of the bijection.

### `(9)` derived from the interface, and `(10)`'s union bound proved

Two modules, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/SharedSectorLimit.lean` — `MRBilinearAt f X hh`, the interface at a *moving* pair
  of parameters (Matomäki–Radziwiłł's uniformity is what lets it be applied at `(x/p², h/p)`), with
  `MRBilinear_iff` showing the unrescaled interface is its instance at the identity.  Then
  `tendsto_sqrt_div_sq`, `tendsto_blockMean_coprime` (the `(8)` limit at the rescaled scale) and

      tendsto_sharedSector_of_MR :
        MRBilinearAt (μ²·1_{p∤·}) (x ↦ x/p²) (x ↦ h(x)/p)  →
          C_p(x,h)/(h√x log 2) → D²/(p+1)².

  This is the card's `(9)`.  The constant works out as `(D·p/(p+1))²/p² = D²/(p+1)²`, the `1/p²`
  being the Jacobian of the rescaling bijection.
- `RHTower/Sieve/NoncoprimeUnionBound.lean` — `sum_union_le_of_nonneg`,
  `sum_biUnion_le_of_nonneg` (neither is in mathlib; the union bound for a nonnegative weight
  follows from `Finset.sum_union_inter`), `noncoprimePairCount`, `exists_shared_prime`, and

      noncoprimePairCount_le :  B(x,h) ≤ ∑_{p ≤ 2√x} C_p(x,h).

  The card's `(10)`, as an exact finite inequality.  A noncoprime balanced pair has `gcd ≥ 2` — no
  squarefreeness needed — and its prime factor divides `n₁ ≤ 2√x`, so the index range is forced.

Combined with `exists_shared_prime_tail_small` (`(11)`) and `coprimeSharedPrimeDensity_le` (`(13)`),
the only step of the card still to assemble is the passage `(10)+(11)+(9) ⟹ (12)`, which is a
limsup interchange over the prime cut-off `P`, and then `(7)+(12)+(13) ⟹ (3)` via
`le_liminf_after_deletion`.  Both are pure limit bookkeeping over pieces that are now all in Lean.

### The prime range splits at the cut-off

`RHTower/Sieve/PrimeRangeSplit.lean`, unconditional, `[propext, Classical.choice, Quot.sound]`:

- `disjoint_primesLE_bigPrimeSet`, `primesLE_eq_union` — `primesLE Q = primesLE P ⊎ bigPrimeSet P Q`
  for `P ≤ Q`, an exact disjoint decomposition.
- `sum_primesLE_split`, and

      noncoprimePairCount_le_split :
        B(x,h) ≤ ∑_{p ≤ P} C_p(x,h) + ∑_{P < p ≤ 2√x} C_p(x,h).

This is the shape the card's step 3 consumes: the first sum is a *finite* sum of terms each of which
has a limit by `(9)`, and the second is what `(11)` makes small uniformly.

#### The one remaining unconditional gap

To feed `(11)` the second sum must be compared with the tail bound it estimates, i.e.

    sharedSectorCount x h p ≤ (√x/p + 1)·(h/p + 1).

The corpus's `card_pair_dvd_le` proves exactly this for a *product* of two independent interval
multiple-counts.  The balanced pair set is not such a product: for fixed `n₁` the second entry
ranges over `[x/n₁, (x+h√x)/n₁]`, an interval whose length is `h√x/n₁ ≤ h` because `n₁ ≥ √x`.  So the
missing step is the nested-sum decomposition of `balancedPairs` — writing it as a sum over `n₁` of
an inner interval count — after which `card_pair_dvd_le`'s inner estimate applies with the uniform
length bound `h`.  That is the next unconditional target; everything downstream of it is already
built.

### The nested decomposition, and the inner interval count

`RHTower/Sieve/BalancedPairsNested.lean`, unconditional,
`[propext, Classical.choice, Quot.sound]`:

- `Icc_eq_Ioc_pred` (`Icc a b = Ioc (a-1) b` for `a ≥ 1`) and `card_filter_dvd_Icc_le`:

      #{n ∈ [a,b] : p ∣ n}  ≤  (b - a + 1)/p + 1,

  the corpus's `Ioc` estimate transported to a closed interval.
- `sum_balancedPairs_filter_nested` — a sum over the balanced pair set, further filtered by any
  predicate, is a sum over the first entry of a sum over the second.  This is the decomposition the
  card's `(10)` needs; the pair set is a filter of a product, so it is `Finset.sum_product` plus
  `Finset.sum_filter`.
- **`inner_count_le`** — for `x ≥ 4`, `h ≥ 0` and `√x ≤ n₁ ≤ 2√x`,

      #{n₂ : x ≤ n₁n₂ ≤ x + h√x, p ∣ n₂}  ≤  (h + 2)/p + 1.

  The point is the length estimate: the `n₂`-interval is `[x/n₁, (x+h√x)/n₁]`, of length
  `h√x/n₁ ≤ h` **because `n₁ ≥ √x`** — the hypothesis that makes the balanced range balanced.  The
  `+2` comes from the two floors (`⌊x/n₁⌋` can undershoot by `1`, and a closed interval carries a
  `+1`); it is harmless because the tail estimate `sum_pair_tail_le` accepts arbitrary
  `l₁, l₂ ≥ 0`, so it will be instantiated at `l₁ = √x + 2`, `l₂ = h + 2` instead of `√x`, `h`, and
  `(√x+2)(h+2)/(h√x) → 1` leaves the limit unchanged.

Remaining for `(12)`: the outer count `#{n₁ ∈ [√x, 2√x] : p ∣ n₁} ≤ (√x+2)/p + 1` (the same
`card_filter_dvd_Icc_le` at the outer interval), assembling the two into
`C_p ≤ ((√x+2)/p + 1)((h+2)/p + 1)`, and re-instantiating the `(11)` limit at `(√x+2, h+2)`.

### `(10)` and `(11)` are fully proved — the MR-free part of the card is complete

Two modules close the gap flagged in the previous section, both unconditional,
`[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/SharedSectorBound.lean` — `moebius_pair_weight_le_one`, `outer_count_le`
  (`#{n₁ ∈ [√x,2√x] : p ∣ n₁} ≤ (√x+2)/p + 1`), and **`sharedSectorCount_le_product`**:

      C_p(x,h) ≤ ((√x + 2)/p + 1)·((h + 2)/p + 1).

  This is the card's `(10)`.  The proof is the nested decomposition, the outer interval count, and
  `inner_count_le` — whose length bound `h√x/n₁ ≤ h` is exactly where `n₁ ≥ √x` is used.
- `RHTower/Sieve/SharedSectorTail.lean` — `sharedSector_tail_le`,
  `sharedSector_tail_normalized_le`, and **`exists_sharedSector_tail_small`**:

      ∀ ε > 0, ∃ P ≥ 1, eventually  (∑_{P < p ≤ 2√x} C_p)/(h√x) ≤ ε.

The tail step reuses the earlier excess limit *verbatim*: bounding `√x + 2 ≤ 3√x` and `h + 2 ≤ 3h`
turns the normalised tail into `9/P + 3·E(x)` with `E` the quantity already proved to vanish.  The
constant degrades from `1/P` to `9/P`, which `(11)` does not care about — it only needs the tail to
vanish as the cut-off grows.  The sharp `D²A` of `(12)` comes from the *small* primes via `(9)`, not
from here.

#### The card's numbered equations, final status

| eq | content | Lean |
|----|---------|------|
| (5) | Matomäki–Radziwiłł Theorem 2 | `MRBilinear` / `MRBilinearAt` — **the sole gate** |
| (6),(7) | densities → signed/absolute pair counts | `tendsto_signClass_of_MR`, from (5) |
| (8) | `p`-deleted squarefree density | **proved** |
| (9) | shared-prime sector density | bijection **proved**; limit `tendsto_sharedSector_of_MR`, from (5) |
| (10) | sector ≤ product of interval counts | **proved** |
| (11) | uniform large-prime tail | **proved** |
| (12) | noncoprime pairs `≤ D²A` | union bound + split **proved**; limit needs (9) |
| (13) | `A ≤ 13/36 < 1/2` | **proved** |
| step 1 | `∑μ = o`, `∑μ² ~ D` over `[√x,2√x]` | **proved** |

**Every statement in the card that does not pass through `(5)` is now an unconditional Lean
theorem.**  What remains is the limsup assembly of `(12)` from `(9)`+`(11)` and of `(3)` from
`(7)`+`(12)`+`(13)`, both of which consume `(5)` through `(9)` and are pure limit bookkeeping over
pieces that are all in Lean (`le_liminf_after_deletion` is already there for the last step).

## The card is formalized end to end

Three modules complete the chain, all unconditional, `[propext, Classical.choice, Quot.sound]`:

- `RHTower/Sieve/NoncoprimeDensity.lean` — `sum_sector_density_le` (every partial sum of the sector
  densities is `≤ D²A`, from `summable_primeSuccInvSq.sum_le_tsum`) and **`eventually_noncoprime_le`**,
  the card's `(12)`:

      ∀ ε > 0, eventually  B(x,h)/(h√x log 2) ≤ D²·A + ε.

- `RHTower/Sieve/CoprimeSignDensity.lean` — `coprimeSignClass`, `weight_eq_one_of_sign`,
  **`signClassCount_sub_le`** (deleting the noncoprime pairs from a sign class costs at most `B` —
  an exact Finset split, using that a pair of product sign `±1` has squarefree weight exactly one),
  `squarefreeDensity_pos`, **`eventually_coprimeSignClass_ge`** and `coprime_margin_pos`.

- `RHTower/Sieve/RouteEMain.lean` — the capstone:

      route_e_sign_density :
        MRBilinear μ hh → MRBilinear μ² hh → (∀ p prime, MRBilinearAt (μ²·1_{p∤·}) …) →
          ∀ ε > 0, eventually
            D²/2 - D²·A - ε ≤ R_ε(x,h)/(h√x log 2)

      route_e_margin_pos :  0 < D²/2 - D²·A

      route_e_signClass_nonempty :
        … → eventually (coprimeSignClass x (h x) ε).Nonempty

`route_e_sign_density` **is** the card's equation `(3)`, and `route_e_signClass_nonempty` is its
stated consequence: every sufficiently large balanced window carries a coprime squarefree pair of
each product sign.

### Status

The card is formalized end to end.  Its entire logical chain — `(5) ⟹ (6) ⟹ (7)`,
`(8) ⟹ (9)`, `(10) + (11) ⟹ (12)`, `(7) + (12) + (13) ⟹ (3)` — is machine-checked, and **every
hypothesis of the capstone is an instance of Matomäki–Radziwiłł's published Theorem 2** at one of
three weights (`μ`, `μ²`, `μ²·1_{p∤·}`), recorded as the named `Prop`s `MRBilinear` / `MRBilinearAt`.

Nothing else is assumed.  The constants are the card's own: `D = 6/π²` (`squarefreeDensity_eq`),
`A ≤ 13/36 < 1/2` (`coprimeSharedPrimeDensity_le`), and the margin `D²(1/2 - A) > 0`
(`route_e_margin_pos`).

## Discharging `(5)`: the state of the Matomäki–Radziwiłł layer

With the card assembled, the only remaining work is to prove `MRBilinear` itself.  A survey of the
corpus's MR-adjacent layer found one **stale gap note**:

`RHTower/Sieve/DirichletDiagonal.lean` says of its double-sum bound that "the entire content still
missing is a bound for the right-hand side, which is a Hilbert inequality for the frequencies
`log n`".  That content is **already proved** elsewhere in the corpus:

- `RHTower/OffDiagonalBound.lean` — `abs_log_ratio_ge`, `inv_abs_log_le`, `sum_inv_dist_le`
  (the harmonic row bound `∑_{n≠m} 1/|n−m| ≤ 2∑_{j≤K} 1/j`), and

      offDiagonal_le :  ∑_m ∑_{n≠m} 2|e_m e_n|/|log n − log m|
                          ≤ 4K·(∑_{j≤K} 1/j)·∑_k e_k²,

  for coefficients supported on `[1,K]`.  This is exactly the mean value theorem's off-diagonal
  estimate, in the elementary `K log K` form (not the sharp Montgomery–Vaughan `K`), which is what
  `LogSeparation.lean`'s own header says the elementary route costs.

The two are separated only by an **index bridge**: `DirichletDiagonal` indexes by `Fin N` with
`n ↦ n+1`, `OffDiagonalBound` by `Finset ℕ ⊆ Icc 1 K`.  Combining them gives, unconditionally,

    | ∫₀^T |∑_{n≤N} a_n n^{it}|² dt − T·∑|a_n|² |  ≤  4N(1 + log N)·∑|a_n|²,

the mean value theorem for Dirichlet polynomials.  That is the next target on the `(5)` path, and it
is bookkeeping, not mathematics.

A duplicate of the harmonic row bound was started and discarded on discovering `OffDiagonalBound`;
recorded here so it is not attempted a third time.

### The integral mean value theorem for Dirichlet polynomials is proved

`RHTower/Sieve/DirichletIntegralMeanValue.lean`, unconditional,
`[propext, Classical.choice, Quot.sound]`:

- `image_succ_univ`, `succ_injOn`, `sum_fin_eq_sum_Icc`, `image_succ_erase`,
  `sum_fin_erase_eq_sum_Icc_erase` — the index bridge `Fin N ↔ [1,N]` via `m ↦ m+1`, for plain and
  punctured sums.
- `coeffAbs`, `coeffAbs_succ`, `coeffAbs_nonneg` — the coefficient moduli extended to `ℕ`.
- **`norm_integral_normSq_dirPoly_sub_diag_le_explicit`** and
  **`norm_integral_normSq_dirPoly_sub_diag_le_log`**:

      | ∫₀^T |∑_{n ≤ N} a_n n^{it}|² dt − T·∑|a_n|² |  ≤  4N·(∑_{j≤N} 1/j)·∑|a_n|²
                                                       ≤  4N(1 + log N)·∑|a_n|².

This closes the gap `DirichletDiagonal.lean` states as "the entire content still missing"; the
content was already in `RHTower/OffDiagonalBound.lean` (a different cone) and only the index bridge
was outstanding.  The elementary `N log N` in place of Montgomery–Vaughan's `N` is exactly what the
logarithmic separation `|log n − log m| ≥ |n−m|/N` costs — no Hilbert inequality enters.

It is the continuous companion of the existing `DirichletMeanValue.lean`, which bounds a *discrete*
mean square over separated frequencies; the two are different theorems and both are now available.

This is the first analytic input of the `(5)` programme.  The remaining stated gaps on that path are
`HalaszDichotomy`/`HalaszWindow` (no lower bound on the distance `δ`, and no identification of the
exceptional frequency), `DirichletRow` (the estimate for `∑_{n ≤ N} n^{iu}` at `u ≠ 0`), and
`BilinearMultiplier` (`HarmonicSineBound`).

### CORRECTION: the Gram row estimate was already proved

The previous section of this card claimed that `RHTower/Sieve/DirichletRowBound.lean` closed the
gap stated in `DirichletRow.lean`.  **That claim was wrong and the module has been deleted.**

`RHTower/Sieve/ZeroLineSum.lean` already contains the estimate, as `norm_sum_zpow0_le`:

    ‖∑_{n ≤ N} n^{iv}‖  ≤  (N + 2)/‖1 + iv‖ + |v|·(1 + log N),

with the `zpow0` / `Zpow0` Euler–Maclaurin layer in `ZeroLinePower.lean`, and
`DirichletFarField.lean` already consumes it to bound the Gram entries
`⟪dirRow N t, dirRow N u⟫`.  `DirichletRow.lean`'s header note ("what remains analytic — and is not
proved here — is the estimate for `∑_{n ≤ N} n^{iu}`") is therefore **stale**, like the other three.

The duplicate additionally re-declared `abs_le_norm_one_add_mul_I`, which `DirichletFarField.lean`
already declares in the same namespace; it compiled only because the two modules do not import each
other, and would have broken the umbrella.  Deleted and unwired.

### The four stated gaps on the `(5)` path: final audit

| module | stated gap | truth |
|---|---|---|
| `DirichletDiagonal` | "the entire content still missing is a Hilbert inequality" | **stale** — `OffDiagonalBound.offDiagonal_le`; only the index bridge was open, now built as `DirichletIntegralMeanValue.lean` |
| `DirichletRow` | "the estimate for `∑ n^{iu}` at `u ≠ 0`" | **stale** — `ZeroLineSum.norm_sum_zpow0_le` |
| `BilinearMultiplier` | "specialising the symbol … is what remains" | **stale** — `HilbertBilinear.hilbert_bilinear_bound` |
| `HalaszDichotomy`, `HalaszWindow` | no lower bound on `δ`; the exceptional frequency is not identified | **real** |

Three of the four were already closed elsewhere in the tree.  The single genuine obstruction on the
path to `MRBilinear` is the Halász analytic half: a lower bound on the Granville–Soundararajan
distance `δ`, and the identification of the exceptional frequency.  Everything feeding into it —
the mean value theorem, the Gram rows, the Hilbert bilinear bound, the distance triangle inequality,
Ramaré, the large sieve — is built.

### First step on the real gap: zeta on a compact box right of the one-line

`RHTower/Sieve/ZetaBoxLowerBound.lean`, unconditional,
`[propext, Classical.choice, Quot.sound]`:

- `box_ne_one`, `one_le_re_box`, and **`exists_pos_lower_bound_zeta_box`**:

      ∀ ε > 0, T ≥ ε, η ≥ 0,  ∃ c > 0,  ∀ σ ∈ [1, 1+η], ∀ t ∈ [ε, T],  c ≤ ‖ζ(σ + it)‖.

- **`le_tsum_re_prime_cpow_box`**:

      ∑'_p cos(t log p)/p^σ  ≥  log c − ∑'_p p^{−2σ},
      uniformly for σ ∈ (1, 1+η], t ∈ [ε, T].

This repairs a mismatch that blocked the two existing pieces from meeting.
`ZetaOneLineBound.exists_pos_lower_bound_zeta_one_line` bounds `‖ζ‖` below on a compact *segment* of
the line `re s = 1`; `ZetaLogPrimeSum.abs_log_norm_riemannZeta_sub_tsum_re_le` compares `log‖ζ‖` with
the prime sum only for `re s > 1`.  The segment carries no `σ > 1`, so the bound could not be fed to
the comparison.  Thickening the segment to a box fixes it: the box is still compact, `ζ` is still
continuous there (the pole is excluded by `t ≥ ε > 0`) and still nonvanishing (`re s ≥ 1`).

This is the compact form of what `MoebiusDistance.lean` calls "the zero-free-region input the corpus
does not have" — and it shows that input is only needed *uniformly in `T`*: on any fixed frequency
range it is elementary.  The constant `c` degrades as `T` grows, which is precisely the reason a
genuine zero-free region is still required for the Halász estimate at frequencies growing with `N`.

### The "zero-free-region input" is in the corpus — uniformly in the frequency

`RHTower/Sieve/ZetaStripPrimeSum.lean`, unconditional,
`[propext, Classical.choice, Quot.sound]`:

- `le_tsum_re_prime_cpow_of_log_le` — any lower bound `L` for `log‖ζ(σ+it)‖` transfers to the prime
  sum with the numeric tail `π²/6` (from `ZetaThreeFourOne.tsum_prime_rpow_le`):

      L − π²/6  ≤  ∑'_p cos(t log p)/p^σ.

- **`le_tsum_re_prime_cpow_strip`** — on the corpus's zero-free strip
  `|σ − 1| ≤ A/log⁹|t|`, `|t| ≥ 9`, `σ > 1`:

      ∑'_p cos(t log p)/p^σ  ≥  −log((20/A)·log⁷|t|) − π²/6,

  **uniformly in `t`**.

`MoebiusDistance.lean`'s note that this is "the zero-free-region input the corpus does not have" is
**stale** — the corpus proved the zero-free region (`RHTower/ZetaLogDerivBound.norm_inv_riemannZeta_le`,
used throughout the prime-number-theorem work on this card), and `riemannZeta_ne_zero_strip` supplies
the nonvanishing that turns `‖1/ζ‖ ≤ B` into `log‖ζ‖ ≥ −log B`.

Only a `log log|t|` is lost, which is what a Halász estimate absorbs.  This supersedes the compact
box bound of the previous section: the box version is elementary but its constant degrades with the
frequency range, whereas this one does not.

Five of the corpus's own gap notes on the `(5)` path have now been checked; four were stale.  What
remains for `MRBilinear` is to run the Halász argument itself on these inputs — the distance lower
bound for `μ` from this prime sum, then the passage from the damped Dirichlet series to the partial
sums.

### The abscissa shift is free

`RHTower/Sieve/PrimeSigmaShift.lean`, unconditional,
`[propext, Classical.choice, Quot.sound]`:

- `one_sub_exp_neg_mem` — `0 ≤ 1 − e^{−u} ≤ u` for `u ≥ 0`.
- **`inv_sub_rpow_le`** — the pointwise shift, for `p ≥ 2` and `σ ≥ 1`:

      0 ≤ 1/p − p^{−σ} ≤ (σ − 1)·log p / p.

- **`abs_sum_weight_shift_le`** — summed against any weights of modulus at most one, using
  `MertensFirst.mertensFirst_upper` (`∑_{p ≤ z} log p/p ≤ log z + log 4`):

      | ∑_{p ≤ z} w_p (1/p − p^{−σ}) |  ≤  (σ − 1)·(log z + log 4).

At the standard choice `σ = 1 + 1/log z` the right side is `1 + log 4/log z`: **the shift between
the `1/p` weighting the distance uses and the `p^{−σ}` weighting the Euler comparison requires costs
only a bounded constant.**  That is the first of the two comparisons separating
`ZetaStripPrimeSum.lean` from a lower bound on the Möbius distance.

The second is the tail `∑_{p > z} p^{−σ}` at the same `σ`, which is likewise bounded — that is the
next target.  With both in hand, `D(μ, χ_t; p ≤ z)² ≥ ∑_{p≤z} 1/p − O(log log|t|)` follows from
`le_tsum_re_prime_cpow_strip`, and `MoebiusDistance`'s missing lower bound is supplied.

#### The remaining piece, stated exactly

The Möbius distance lower bound now reduces to a single unproved estimate:

    ∑_{p > z} p^{−σ}  =  O(1)   at   σ = 1 + 1/log z.                          (T)

Given `(T)`, the chain closes:

    ∑_{p ≤ z} cos(t log p)/p
      ≥ ∑_{p ≤ z} cos(t log p)·p^{−σ}  −  (σ−1)(log z + log 4)     [PrimeSigmaShift]
      ≥ ∑'_p cos(t log p)·p^{−σ}  −  ∑_{p>z} p^{−σ}  −  (1 + log 4/log z)
      ≥ −log((20/A)·log⁷|t|) − π²/6 − O(1),                        [ZetaStripPrimeSum]

whence `D(μ, χ_t; p ≤ z)² = ∑_{p≤z}(1 + cos(t log p))/p ≥ ∑_{p≤z} 1/p − O(log log|t|)`, and
`MoebiusDistance.lean`'s missing lower bound is supplied.

**`(T)` is not available in the corpus and is not elementary.**  Checked: there is no prime-tail
bound of this shape, and no Chebyshev `π(x) ≪ x/log x`.  The naive comparison fails —
`∑_{n>z} n^{−σ} ≤ z^{1−σ}/(σ−1) = e^{−1} log z`, a full logarithm too large — so the prime density
is essential.  Nor does rescaling help: `σ − 1 = c/log z` is forced, since a smaller exponent makes
the tail grow and a larger one makes the shift cost exceed the `o(log log z)` budget.

The route is summation by parts against Mertens' second theorem (`MertensSecond.mertensS_le`,
`le_mertensS`, both in the corpus, and `AbelInequality`/`AbelTail` for the machinery):

    ∑_{z<p≤Y} p^{−1}·x^{−(σ−1)}  =  A(Y)g(Y) + ∫_z^Y A(x)(σ−1)x^{−σ} dx,
    A(x) = ∑_{z<p≤x} 1/p = log log x − log log z + O(1/log z),

and the substitution `x = z^u` turns the integral into `∫_1^∞ (log u + C)e^{−u} du = O(1)`.  Note the
corpus's Abel *inequality* (bounded partial sums against a monotone weight) does **not** apply here:
`A(x)` is unbounded.  The full summation-by-parts identity is needed.

That is the next target, and it is the last analytic step before the Möbius distance bound.

### Toward `(T)`: the dyadic prime window

`RHTower/Sieve/PrimeWindowDyadic.lean`, unconditional,
`[propext, Classical.choice, Quot.sound]`:

- `one_sub_exp_neg_ge` — `u/2 ≤ 1 − e^{−u}` on `[0,1]`, via `e^{−u} ≤ 1/(1+u)`.  This controls the
  ratio `2^{−(σ−1)}` of the geometric series in the dyadic sum: it gives
  `1 − 2^{−(σ−1)} ≥ (σ−1)log 2/2`, hence `∑_k 2^{−k(σ−1)} ≤ 2/((σ−1)log 2) = 2 log z/log 2`.
- `logLog_two_mul_sub_le` — `logLog(2y) − logLog y ≤ log 2/log y`, i.e. `log(1 + log2/log y) ≤ log2/log y`.
- **`sum_inv_dyadic_window_le`** —

      ∑_{y < p ≤ 2y} 1/p  ≤  (log 2 + 2C)/log y,     C = 2·mertensFirstConst + 1/2.

The last is the pivotal estimate and it is why `MertensWindowSharp.lean` had to exist.  A one-sided
Mertens bound gives only `O(1)` per dyadic block, and there are `≍ log z` blocks below the point
where the geometric factor takes over — that route yields `O(log z)` and fails.  The **decaying**
error of the sharp form gives `O(1/log y)` per block, and the product with the geometric factor sums
to `O(1)`.  This is exactly the trap the corpus's own `MertensWindowSharp` header warns about
("subtracting two one-sided Mertens bounds adds their additive constants, which is fatal for a
window of bounded ratio").

Remaining for `(T)`: assemble the blocks — partition the primes above `z` into the dyadic windows
`(2^k z, 2^{k+1} z]`, apply `sum_inv_dyadic_window_le` and `p^{−(σ−1)} ≤ (2^k z)^{−(σ−1)}` on each,
and sum the resulting geometric series with `one_sub_exp_neg_ge`.  Both ingredients of that final
step are now in place; what is left is the partition bookkeeping.

### The dyadic tower is assembled

`RHTower/Sieve/PrimeTailBound.lean`, unconditional,
`[propext, Classical.choice, Quot.sound]`:

- `bigPrimeSet_split`, `bigPrimeSet_split_disjoint` — a prime window splits at any interior point,
  disjointly.
- **`sum_rpow_dyadic_block_le`** — on one dyadic window, for `σ > 1`:

      ∑_{y < p ≤ 2y} p^{−σ}  ≤  y^{−(σ−1)}·(log 2 + 2C)/log y,

  since `p^{−σ} = p^{−(σ−1)}·p^{−1} ≤ y^{−(σ−1)}·p^{−1}` and the window's reciprocal sum is the
  previous section's estimate.
- **`sum_rpow_bigPrimeSet_pow_le`** — the tower, by induction on `K`:

      ∑_{z < p ≤ 2^K z} p^{−σ}  ≤  ∑_{k < K} (2^k z)^{−(σ−1)}·(log 2 + 2C)/log(2^k z).

The induction is clean because the split is exact: `bigPrimeSet z (2^{K+1}z)` is the disjoint union
of `bigPrimeSet z (2^K z)` and `bigPrimeSet (2^K z) (2·2^K z)`, so the inductive hypothesis and one
block bound add with no loss.

What remains for `(T)` is to collapse the right-hand side: bound `1/log(2^k z) ≤ 1/log z` and
`(2^k z)^{−(σ−1)} = z^{−(σ−1)}·(2^{−(σ−1)})^k ≤ (2^{−(σ−1)})^k`, then sum the geometric series with
`one_sub_exp_neg_ge`, giving `2(log 2 + 2C)/((σ−1)·log z·log 2)` — the constant
`2(log 2 + 2C)/log 2` at `σ = 1 + 1/log z`.  Every ingredient of that collapse is now a theorem;
only the arithmetic remains.

### `(T)` is proved

`RHTower/Sieve/PrimeTailBound.lean` (continued), unconditional,
`[propext, Classical.choice, Quot.sound]`:

- `rpow_two_pow_mul` — `(2^k z)^{−(σ−1)} ≤ (2^{−(σ−1)})^k`, since `z^{−(σ−1)} ≤ 1`.
- **`sum_rpow_bigPrimeSet_le_const`** — for `z ≥ 2`, `1 < σ`, `σ − 1 ≤ 1`, uniformly in `K`:

      ∑_{z < p ≤ 2^K z} p^{−σ}  ≤  ((log 2 + 2C)/log z) · 2/((σ−1)·log 2).

- **`sum_rpow_bigPrimeSet_le_abs`** — at the standard abscissa `σ = 1 + 1/log z` (`z ≥ 3`):

      ∑_{z < p ≤ 2^K z} p^{−(1 + 1/log z)}  ≤  2(log 2 + 2C)/log 2,

  **an absolute constant, uniform in `z` and in the truncation.**

This is `(T)`.  The two factors cancel exactly as designed: the per-block decay `1/log z` from the
sharp Mertens window against the geometric sum `2/((σ−1)log 2) = 2 log z/log 2` from
`one_sub_exp_neg_ge`.  Neither factor alone is bounded; only the product is, and it is bounded by a
constant with no residual dependence on `z`.

#### Consequence: the Möbius distance lower bound is now in reach

With `(T)` and `PrimeSigmaShift.abs_sum_weight_shift_le`, the chain recorded earlier closes:

    ∑_{p ≤ z} cos(t log p)/p  ≥  −log((20/A)·log⁷|t|) − π²/6 − 2(log 2 + 2C)/log 2 − (1 + log 4/log z),

so `D(μ, χ_t; p ≤ z)² = ∑_{p≤z}(1 + cos(t log p))/p ≥ ∑_{p≤z} 1/p − O(log log|t|)` — the lower bound
`MoebiusDistance.lean` records as missing.  What remains is to assemble these four inequalities and
to pass from the tower truncation `2^K z` to all primes above `z`.

#### `(T)` in usable form

`bigPrimeSet_mono` and **`sum_rpow_bigPrimeSet_le_abs'`** remove the tower restriction: for **every**
upper limit `Y`, not just `Y = 2^K z`,

    ∑_{z < p ≤ Y} p^{−(1 + 1/log z)}  ≤  2(log 2 + 2C)/log 2,

because any `Y` is covered by the tower (`Y < 2^Y ≤ 2^Y·z`) and the terms are nonnegative.

#### The one remaining mismatch

The strip bound `le_tsum_re_prime_cpow_strip` is a statement about `∑'` over **all** primes — it comes
from the Euler product, so it cannot be localised to a window.  Subtracting the tail therefore needs
`(T)` in `tsum` form:

    ∑'_{p > z} p^{−σ}  ≤  2(log 2 + 2C)/log 2,

which follows from the finite version by `tsum_le_of_sum_le` (all finite subsums are bounded, terms
are nonnegative), given summability of `p ↦ p^{−σ}` over `Nat.Primes` for `σ > 1`.

That conversion is the next step.  It is pure plumbing — mapping a `Finset Nat.Primes` into a
`bigPrimeSet` window through the coercion `Nat.Primes → ℕ` — with no analytic content, and it is the
last item before the four inequalities assemble into

    D(μ, χ_t; p ≤ z)²  ≥  ∑_{p ≤ z} 1/p − O(log log|t|).

### The Möbius distance lower bound is proved

The four inequalities are now assembled.  Three new modules, all unconditional
(`[propext, Classical.choice, Quot.sound]`).

**`RHTower/Sieve/PrimeTailBound.lean` (continued) — `(T)` as a `tsum`.**

- `primeTailTerm z σ p = if z < p then p^{−σ} else 0`, with `primeTailTerm_nonneg` and
  `summable_primeTailTerm` (comparison with `Real.summable_nat_rpow` composed with
  `Nat.Primes.coe_nat_injective`).
- **`tsum_primeTailTerm_le`** — for `z ≥ 3`,

      ∑'_{p prime, p > z} p^{−(1 + 1/log z)}  ≤  2(log 2 + 2C)/log 2.

  The passage from the finite bound is `isLUB_hasSum`: every finite subsum of a nonnegative family
  is at most the constant, so the sum, being the least upper bound of the finite subsums, is too.
  Each finite `Finset Nat.Primes` maps into the window `bigPrimeSet z Y` with `Y` its own supremum,
  where `sum_rpow_bigPrimeSet_le_abs'` applies.  (mathlib's `tsum_le_of_sum_le` does not exist on
  this toolchain; `isLUB_hasSum` is the working replacement.)

**`RHTower/Sieve/PrimeCosineSum.lean` — the cosine sum on the one-line.**

- `primeSubtypeLE z` — the primes up to `z` as a `Finset Nat.Primes`, with `mem_primeSubtypeLE` and
  `sum_primeSubtypeLE` transporting sums to `Nat.primesLE z`.  (`Nat.Primes` is a `def`, not an
  abbreviation, so `rw` with `Finset.mem_subtype` / `Finset.sum_subtype_eq_sum_filter` fails at
  `instances` transparency; both must be applied in term mode.)
- `norm_prime_tail_re_le`, **`tsum_re_prime_cpow_split`** — the head–tail split

      ∑'_p Re(p^{−(σ+it)})  =  ∑_{p ≤ z} p^{−σ} cos(t log p)  +  ∑'_{p > z} Re(p^{−(σ+it)}),

  the head evaluated through the corpus's `RHTower.re_natCast_cpow_neg`.
- **`abs_tsum_prime_tail_re_le`** — the truncation error is at most `∑' primeTailTerm z σ`.
- **`sum_cos_div_prime_ge`** — for `z ≥ 3`, `|t| ≥ 9` and `1/log z ≤ A/log⁹|t|`,

      ∑_{p ≤ z} cos(t log p)/p  ≥  −log((20/A)·log⁷|t|) − π²/6 − 2(log 2 + 2C)/log 2 − (1 + log 4).

  This is the estimate `MoebiusDistance.lean` recorded as "the zero-free-region input the corpus does
  not have".  It is unconditional and uniform in the frequency.

**`RHTower/Sieve/MoebiusFrequencyDistance.lean` — the distance at every frequency.**

- `mulDistSqPair_neg_one_split` — `D(f, χ_t; P)² = ∑_P 1/p + ∑_P cos(t log p)/p` for `f = −1` on `P`.
- `nine_mul_logLog_le_logLog` — the coupling `1/log z ≤ A/log⁹|t|` forces
  `log log z ≥ 9 log log|t| − log A`.
- `log_strip_bound_eq` — `log((20/A) log⁷|t|) = log(20/A) + 7 log log|t|`.
- **`two_mul_logLog_abs_sub_le_mulDistSqPair`** — for `z ≥ 3`, `|t| ≥ 9`, `1/log z ≤ A/log⁹|t|` and
  `f ≡ −1` on the primes up to `z`,

      D(f, χ_t; p ≤ z)²  ≥  2 log log|t|  −  moebiusFrequencyConst,

  with `moebiusFrequencyConst` absolute.

The coupling between `z` and `t` is a gain, not a cost: the strip demands `log⁹|t|/A ≤ log z`, which
supplies `9 log log|t|` of Mertens mass while the strip loses only `7 log log|t|`.  The surplus
`2 log log|t|` is the content: **the Möbius function is quantitatively far from every character
`χ_t` in the range, not merely from the trivial one.**  This closes the input that
`HalaszDichotomy`/`HalaszWindow` needs on its distance side.

### The frequency range is now covered without a gap

The distance bound above holds at `|t| ≥ 9`.  Halász's mechanism needs the *minimum* over a whole
range `|t| ≤ T`, so the segment `|t| ≤ 9` — which contains the pole of `ζ` — had to be closed too.

**`RHTower/Sieve/ZetaPoleBoxLowerBound.lean`.**  `ZetaBoxLowerBound.lean` minimises `‖ζ‖` on a
compact box, and that argument breaks at `t = 0`, where `ζ` is unbounded.  The repair is to minimise
the *entire* function `zetaEntire s = (s−1)ζ(s)` (already in the corpus, in
`RHTower/BoundedExponentPoissonNonlanding.lean`) instead.

- **`zetaEntire_ne_zero_of_one_le_re`** — `zetaEntire` does not vanish on `re s ≥ 1`: off the pole
  because `ζ` does not, and at `s = 1` because its value there is the residue, `(Γ_ℝ 1)⁻¹ ≠ 0`.
- `norm_sub_one_le_box` — the distance to the pole across the box is at most `η + T₀ + 1`.
- **`exists_pos_lower_bound_zeta_pole_box`** — for every `η, T₀ ≥ 0` there is `c > 0` with
  `c ≤ ‖ζ(σ+it)‖` for all `σ ∈ (1, 1+η]` and `|t| ≤ T₀`.  **The pole helps rather than hinders:**
  `ζ` is *large* near `s = 1`, and dividing the compactness minimum of `|zetaEntire|` by the bounded
  factor `|s−1|` is all that is needed.
- **`exists_sum_cos_div_prime_ge_small`** — hence `∑_{p ≤ z} cos(t log p)/p ≥ −C` for every `z ≥ 3`
  and every `|t| ≤ 9`, with `C` absolute.

To make both branches instances of one statement, `PrimeCosineSum.lean` was refactored: the
truncation and abscissa-shift passage is now the strip-agnostic
**`sum_cos_div_prime_ge_of_le`**, which converts *any* lower bound for `∑'_p Re(p^{−(σ+it)})` at
`σ = 1 + 1/log z` into one for `∑_{p ≤ z} cos(t log p)/p`.  The strip and the pole box are its two
instantiations.

**`RHTower/Sieve/MoebiusUniformFrequency.lean` — the uniform statements.**

- `log_strip_bound_range`, `log_log_range_pos`, `sum_cos_div_prime_ge_range` — the strip bound keyed
  on the range bound `T` rather than on the frequency, by monotonicity of `log`.
- **`exists_sum_cos_div_prime_ge_uniform`** — an absolute `C` with

      ∑_{p ≤ z} cos(t log p)/p  ≥  −7 log log T − C     for **every** `|t| ≤ T`,

  whenever `z ≥ 3`, `T ≥ 9` and `1/log z ≤ A/log⁹T`.  No frequency is excluded.
- **`exists_mulDistSqPair_ge_uniform`** — hence, for `f ≡ −1` on the primes up to `z`,

      min_{|t| ≤ T} D(f, χ_t; p ≤ z)²  ≥  log log z − 7 log log T − C.

- `sum_inv_sq_primesLE_le` — `∑_{p ≤ z} 1/p² ≤ π²/6`, from `hasSum_zeta_two`.
- **`exists_norm_sum_moebius_smooth_le_uniform`** and
  **`exists_norm_sum_moebius_smooth_le_absolute`** — feeding the distance minimum into the corpus's
  damped Euler bound `norm_sum_moebius_smooth_le_exp`,

      ‖∑_{n squarefree, z-smooth} μ(n) n^{−it}/n‖  ≤  C·(log T)⁷      for all `|t| ≤ T`,

  with `C` absolute and the bound **independent of the smoothness parameter `z`**, whereas the
  trivial bound for that sum grows like `log z`.  Under the coupling `log z ≥ log⁹T/A` forced by the
  strip this is a power saving: `(log T)⁷ ≍ (log z)^{7/9}` against the trivial `log z`.

This is the unconditional Halász saving for the Möbius function, and it closes the item that
`HalaszDichotomy.lean` records in its own header as the analytic content the elementary theory does
not supply ("nothing here … bounds `δ` from below").  The remaining step on the Matomäki–Radziwiłł
path is the *mean-value* form of Halász's argument — averaging over `t` rather than bounding
pointwise — since the pointwise Euler estimate cannot decay: it needs `D² > ∑1/p + ∑1/p²`, and the
true `D² = ∑1/p + ∑cos(t log p)/p` leaves `∑1/p² − ∑cos(t log p)/p`, which the bound above makes
`O(log log T)` but never negative.

### The bilinear hypothesis `(5)`, structurally reduced

Four new modules take the card's one external input apart.  All unconditional
(`[propext, Classical.choice, Quot.sound]`).

**`RHTower/Sieve/PairFibre.lean` — the fibre decomposition.**

- `outerBlock x h`, `innerFibre x h a`, with membership lemmas.
- **`pairSum_eq_sum_fibre`** — for every weight, every `x` and every `h`,

      ∑_{(a,b) balanced} f(a)f(b)  =  ∑_{a ∈ block} f(a) · ∑_{b ∈ fibre(a)} f(b).

- **`abs_pairSum_le_sum_abs_fibre`** — for `|f| ≤ 1` the outer weight can be discarded.
- `innerFibre_subset`, **`card_innerFibre_le`** — the fibre above `a` is contained in
  `[⌈x/a⌉, ⌊(x+h√x)/a⌋]` and has at most `h√x/a + 1` elements.

**This exhibits the shape of the theorem.**  The inner sum is a Möbius sum over an interval of
length `h√x/a ∈ [h/2, h]`, and the outer variable moves its *starting point* `x/a` across `√x`
distinct values.  The bilinear all-interval theorem is therefore not a statement about one short
interval — no pointwise statement is true at the card's window lengths — but about the average over
the block of starting points.  That is exactly why an arbitrarily slowly growing `h` is admissible.

**`RHTower/Sieve/HarmonicDyadicBlock.lean` — the constant `log 2`.**

- `sum_Icc_one_div_le_log_sub`, `log_sub_le_sum_Icc_one_div` — the telescoped concavity sandwich
  `log(n+1) − log m ≤ ∑_{m ≤ k ≤ n} 1/k ≤ log n − log(m−1)`.
- floor/ceiling normalisations, and **`tendsto_sum_dyadic_one_div`**:
  `∑_{⌈u⌉ ≤ k ≤ ⌊2u⌋} 1/k → log 2`.

**`RHTower/Sieve/PairFibreTrivial.lean` — the normalisation is the trivial size.**

- **`outerBlock_eq`** — for `x ≥ 4` the block is exactly the integer interval `[⌈√x⌉, ⌊2√x⌋]`.
- `card_outerBlock_le` — it has at most `√x + 1` elements.
- **`abs_pairSum_le_trivial`** — `|pairSum f x h| ≤ h√x ∑_{a ∈ block} 1/a + (√x + 1)`.
- **`tendsto_trivial_bound_ratio`** — for any window length tending to infinity that trivial bound,
  divided by `h√x log 2`, tends to `1`.

So **the card's normalising constant `log 2` is precisely the trivial size of the sum it
normalises** — it is `∑_{a ∈ block} 1/a` in the limit, nothing else.  Any nonzero limit of the
normalised pair sum is a genuine correlation, and `(5)`'s assertion is a statement of total
cancellation against the exact trivial bound.

**`RHTower/Sieve/MRFibreReduction.lean` — the reduction.**

- `AveragedShortInterval f hh` — the `Prop` that the block average of `|∑_{b ∈ fibre(a)} f(b)|` is
  `o(h√x)`.
- `tendsto_pairSum_of_averaged`, `MRBilinear_of_averaged`, and
  **`MRBilinear_moebius_of_averaged`** — for `μ` (whose block mean vanishes) the bilinear
  all-interval theorem **is** the averaged short-interval property, with no loss:

      AveragedShortInterval μ hh  ⟹  MRBilinear μ hh.

The card's `(5)` at `μ` is thus reduced to a single averaged estimate over `√x` short Möbius sums.
The remaining instance is `(5)` at `μ²`, where the block mean is `D` rather than `0`; that reduction
needs in addition the *logarithmic* block mean `∑_{√x < a ≤ 2√x} μ²(a)/a → D log 2`, which is the
next target.

### `(5)` at `μ²` reduced too, and the constant `D²` derived

Five further modules, all unconditional (`[propext, Classical.choice, Quot.sound]`).

**`RHTower/Sieve/SquarefreeGlobalCount.lean`.**  `abs_sum_moebius_sq_Icc_sub_le`:

    | #{n ≤ m : n squarefree} − m·D |  ≤  2√m + 1.

The corpus's window count is uniform in the starting point, so taking the starting point `0` and
`R = ⌊√m⌋ + 1` — the least `R` with `m ≤ R²` — balances its two error halves exactly (`R ≤ √m + 1`
and `m/R ≤ √m`).

**`RHTower/Sieve/HarmonicDyadicBlock.lean` (continued).**  `tendsto_log_sub_log_of_ratio` and
**`tendsto_sum_Icc_one_div_of_ratio`**: the block harmonic limit depends only on the *normalised
growth* of the endpoints, so `∑_{p(u) ≤ k ≤ q(u)} 1/k → log 2` whenever `p(u)/u → 1` and
`q(u)/u → 2`.  Both the block and its shift by one are instances.

**`RHTower/Sieve/SquarefreeLogSum.lean`.**  Abel summation (`HTGeometry.sum_mul_eq_partial_mul_diff`)
against the count:

- `squarefreeLogSum_abel`, **`squarefreeLogSum_eq`** — the exact split into
  `D ∑_{m ≤ N} 1/(m+1)`, an error sum, a drift term and a boundary term;
- `sum_Icc_telescope_inv` — `∑_{M < m ≤ N}(1/m − 1/(m+1)) = 1/(M+1) − 1/(N+1)`, which is what makes
  the error sum collapse;
- **`abs_squarefreeLogSum_sub_le`** — the block difference loses only
  `(3(2√N + 1) + D)/(M+1)`;
- **`tendsto_squarefree_block_log_mean`** —

      ∑_{⌈u⌉ ≤ a ≤ ⌊2u⌋} μ²(a)/a  →  D · log 2.

**`RHTower/Sieve/MRFibreDensity.lean`.**  `AveragedShortIntervalDensity f c hh` — the fibre sums
agree with `c` times their lengths, on average over the block — and

- `abs_pairSum_sub_main_le` — the pair sum against its density main term;
- **`MRBilinear_moebius_sq_of_averaged`** —

      AveragedShortIntervalDensity μ² D hh  ⟹  MRBilinear μ² hh.

**The constant is derived, not assumed.**  The main term is `D·h√x·∑_{a ∈ block} μ²(a)/a`, which the
logarithmic block mean turns into `D·(D log 2)/log 2 = D²` — exactly the squared block mean the
bilinear theorem asserts.  Nothing about `D²` enters as a hypothesis.

**`RHTower/Sieve/RouteEAveraged.lean` — the capstone restated.**
**`route_e_sign_density_of_averaged`** and **`route_e_signClass_nonempty_of_averaged`** prove the
card's `(3)` and its consequence with `hMR1`, `hMR2` replaced by the two averaged estimates

    ∑_{a ∈ block} |∑_{b ∈ fibre(a)} μ(b)|                 = o(h√x),
    ∑_{a ∈ block} |∑_{b ∈ fibre(a)} μ²(b) − D·h√x/a|      = o(h√x).

So two of the card's three external inputs are now single averaged short-interval estimates about one
arithmetic function each, over the `√x` starting points `x/a`.  The third, `hMRp`, is the same
statement for the weights `μ²·1_{p∤·}` at the rescaled parameters; reducing it the same way is the
next step.

### All three inputs reduced; the Abel layer generalised

**Correction to the previous entry.**  The Abel development first written inside
`SquarefreeLogSum.lean` has been generalised and moved: `weightLogSum_abel`, `weightLogSum_eq`,
`abs_weightLogSum_sub_le`, `sum_Icc_one_split`, `sum_Icc_telescope_inv`, `sum_Icc_shift_one` and the
endpoint limits now live in **`RHTower/Sieve/LogSumFromCount.lean`**, stated for an arbitrary weight.
`SquarefreeLogSum.lean` is now the `μ²` instance only.  The mathematical content is unchanged; the
names `squarefreeLogSum_abel`, `squarefreeLogSum_eq`, `abs_squarefreeLogSum_sub_le` no longer exist.

**`RHTower/Sieve/LogSumFromCount.lean` — the general passage.**  For any weight `f` with

    | ∑_{n ≤ m} f(n) − mc |  ≤  C√m + C,

**`tendsto_block_log_mean_of_count`** gives

    ∑_{⌈u⌉ ≤ a ≤ ⌊2u⌋} f(a)/a  →  c · log 2.

Abel summation trades `1/a` for the partial sums against `1/m − 1/(m+1)`, whose total mass over
`(M, N]` is `1/(M+1) − 1/(N+1)`; the counting error is therefore multiplied by something of size
`1/M`, and `√N/M → 0` across a block of ratio two.  **The natural mean and the logarithmic mean of a
square-root-regular weight agree** — that is the whole reason the normalisation by `h√x log 2`
produces the square of the block mean.

**`RHTower/Sieve/CoprimeLogSum.lean` — the third weight.**
`abs_coprimeSquarefreeWeight_le_one`, **`abs_weightErr_coprime_le`** (the corpus's coprime window
estimate at starting point `0`, with `R = ⌊√m⌋+1`, giving `3√m + 3`), and

    **`tendsto_coprime_block_log_mean`** :  ∑_{⌈u⌉ ≤ a ≤ ⌊2u⌋} μ²(a)·1_{p∤a}/a → (D p/(p+1)) log 2,

which matches `SharedSectorLimit.tendsto_blockMean_coprime` exactly.

**`RHTower/Sieve/MRFibreDensityAt.lean` — the moving pair of parameters.**
`AveragedShortIntervalDensityAt f c X hh`, and **`MRBilinearAt_of_averaged`**: for any unit-bounded
weight whose count is `mc + O(√m)` and whose block mean tends to `c`,

    ∑_{a ∈ block(X)} | (∑_{b ∈ fibre(a)} f(b)) − c·h√X/a | = o(h√X)  ⟹  MRBilinearAt f X hh.

Instantiated at `μ²·1_{p∤·}` and `(X, h) = (x/p², h/p)` this is
**`MRBilinearAt_coprime_of_averaged`** — the card's `hMRp`.

**`RHTower/Sieve/RouteEAveraged.lean` (continued) — the card's `(3)` on averaged estimates alone.**
**`route_e_sign_density_of_averaged_all`** and **`route_e_signClass_nonempty_of_averaged_all`** take
exactly three hypotheses beyond the window law:

    ∑_{a ∈ block} |∑_{b ∈ fibre(a)} μ(b)|                        = o(h√x),
    ∑_{a ∈ block} |∑_{b ∈ fibre(a)} μ²(b) − D·h√x/a|             = o(h√x),
    ∑_{a ∈ block(x/p²)} |∑_{b ∈ fibre(a)} μ²1_{p∤}(b) − D_p·h√x/(pa)| = o(h√x/p)   (each prime `p`),

and prove the card's `(3)` and its consequence.  **Every one of the card's external inputs is now a
single averaged short-interval estimate for one arithmetic function**, over the block of starting
points, with all three constants (`0`, `D²`, `D²/(p+1)²`) derived from logarithmic block means rather
than assumed.  Nothing else about Matomäki–Radziwiłł's theorem is used.

### The inputs are mean squares over short intervals

**`RHTower/Sieve/PairFibreMeanSquare.lean`**, unconditional.

- **`innerFibre_eq`** — for `x ≥ 4` and `a` in the block the fibre is *exactly* the integer interval
  `[⌈x/a⌉, ⌊(x+h√x)/a⌋]`: the ambient bounds `1 ≤ b ≤ ⌊x+h√x⌋` in its definition are implied by the
  product constraint.  So each inner sum is literally a sum of the weight over a short interval, of
  length between `h/2` and `h`, starting at `x/a`.
- **`tendsto_sum_abs_div_of_meanSquare`** — Cauchy–Schwarz over the block: since the block has at
  most `√X + 1` elements,

      (∑_{a ∈ block} |g(a)|)²  ≤  (√X + 1) · ∑_{a ∈ block} g(a)²,

  so a mean-square bound `∑_a g(a)² = o(h²√X)` implies the averaged bound.  Stated once for an
  arbitrary family of deviations at a moving pair of parameters, then instantiated three times.
- `AveragedMeanSquare`, `AveragedMeanSquareDensityAt`, and the three corollaries
  `averagedShortInterval_of_meanSquare`, `averagedShortIntervalDensity_of_meanSquare`,
  `averagedShortIntervalDensityAt_of_meanSquare`.

**`RHTower/Sieve/RouteEAveraged.lean` (continued).**
**`route_e_sign_density_of_meanSquare`** and **`route_e_signClass_nonempty_of_meanSquare`** prove the
card's `(3)` and its consequence from three mean squares:

    ∑_{a ∈ block} (∑_{b ∈ fibre(a)} μ(b))²                       = o(h²√x),
    ∑_{a ∈ block} (∑_{b ∈ fibre(a)} μ²(b) − D·h√x/a)²            = o(h²√x),
    ∑_{a ∈ block(x/p²)} (∑_{b ∈ fibre(a)} μ²1_{p∤}(b) − D_p·h√x/(pa))² = o(h²√x/p²)  (each `p`).

**This is the literature's form.**  A mean square of a short sum over its starting points is exactly
what Matomäki–Radziwiłł's theorem bounds; the fibre decomposition has now carried the card's
statement all the way to it, with every constant derived.

The remaining mismatch is bookkeeping of a known kind: the fibre lengths `⌊(x+h√x)/a⌋ − ⌈x/a⌉ + 1`
vary with `a` between `h/2` and `h`, whereas the standard statement fixes the length.  The starting
points `x/a` are `1`-separated up to a factor `4` (`d(x/a)/da ∈ [−1, −1/4]` on the block), so they
form a genuine sample of starting points rather than a sparse or clustered set.

### The Möbius input is now literally Matomäki–Radziwiłł's statement

**`RHTower/Sieve/FibreStartSeparation.lean`**, unconditional.

The fibre above `a` starts at `⌈x/a⌉`, and across the block

    x/a − x/a'  =  x(a'−a)/(aa')  ≥  x/(4x)  =  1/4      (a < a'),

so the starting points are `1/4`-separated.  The formal handle on this is that

- **`ceil_four_mul_injOn`** — `a ↦ ⌈4x/a⌉` is *injective* on the block (a gap of `1` in the
  quadrupled reciprocal forces distinct ceilings), and
- **`card_fibreStart_preimage_le`** — `⌈x/a⌉ = k` confines `⌈4x/a⌉` to the four values `4k−3, …, 4k`,
  so **at most four elements of the block share a starting point**;
- **`sum_block_comp_start_le`** — hence for nonnegative `G`,

      ∑_{a ∈ block} G(⌈x/a⌉)  ≤  4 ∑_{⌈√x/2⌉ ≤ y ≤ ⌈√x⌉} G(y).

  The fibre family is a genuine sample of starting points: neither sparse nor clustered.

- `maxWindowSq f H y` — the largest squared window sum of length at most `H` starting at `y`;
- **`sum_fibre_sq_le_maximal`** — every fibre is a window of length at most `⌈h⌉` starting at
  `⌈x/a⌉` (this uses `innerFibre_eq` and the length bound `⌊(x+h√x)/a⌋ − ⌈x/a⌉ ≤ h`, valid because
  `a ≥ √x`), so

      ∑_{a ∈ block} (∑_{b ∈ fibre(a)} f(b))²  ≤  4 ∑_{⌈√x/2⌉ ≤ y ≤ ⌈√x⌉} maxWindowSq f ⌈h⌉ y;

- `MaximalWindowMeanSquare f hh` and **`averagedMeanSquare_of_maximal`**.

**`RouteEAveraged.route_e_sign_density_of_maximalWindow`** — the card's `(3)` with the Möbius
hypothesis in the form

    ∑_{√x/2 ≤ y ≤ √x}  max_{m ≤ h} (∑_{y ≤ n ≤ y+m} μ(n))²  =  o(h²√x),

which is exactly the mean square of `μ` over short intervals that Matomäki–Radziwiłł's theorem
bounds — *all* starting points in a dyadic range, window length at most `h`, no reference to the
fibre geometry at all.  **The variable length of the fibres, which is what separated the card's
statement from the literature's, is absorbed by the maximum.**

The two remaining inputs (`μ²` and `μ²·1_{p∤·}`) are still stated as centred fibre mean squares; the
same passage applies to them once the maximal object is centred, the discrepancy between the integer
window length `m+1` and the real fibre length `h√x/a` being at most `2` and hence contributing
`O(√x) = o(h²√x)`.
