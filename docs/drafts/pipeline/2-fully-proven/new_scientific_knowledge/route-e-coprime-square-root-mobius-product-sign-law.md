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
- [ ] distinct-product local Hall capacity
- [ ] co-moving sector flux

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
- [ ] distinct-product local Hall capacity
- [ ] co-moving sector flux

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
