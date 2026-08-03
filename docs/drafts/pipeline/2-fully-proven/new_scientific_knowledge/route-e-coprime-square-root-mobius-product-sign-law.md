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
