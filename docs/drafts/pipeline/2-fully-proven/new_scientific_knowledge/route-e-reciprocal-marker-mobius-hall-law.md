# Route E reciprocal-marker Möbius Hall law

- **ID:** `ROUTE-E-RECIPROCAL-MARKER-HALL-001`
- **Stage:** 2-fully-proven
- **Type:** NEW SYNTHESIS / ALL-INTERVAL DISTINCT-TARGET THEOREM
- **Parent:** `../../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** prime-anchor, window, sign and unique-decoding skeleton in
  `MobiusReciprocalMarkerPrimeCapacity.lean`; the distinct-target count, the Markov step `(10)`,
  the marker discard, the squarefree count `(7)`/`(11)` with density `6/pi^2`, the averaged tail
  `(12)`-`(13)`, the dyadic prime supply and the integer-start comparison are formalized
  unconditionally in `MobiusReciprocalMarkerBlockCount.lean`, `Sieve/SquarefreeCount.lean`,
  `Sieve/AveragedSquarefreeTail.lean`, `Sieve/PrimeWindow.lean`, `Sieve/StartShift.lean`;
  the sole remaining input is Menon's unconditional 2026 Moebius mean-square theorem `(6)`

## Statement

Fix
\[
 \frac12<\beta<1,\qquad
 h(X)=\exp\!\big((\log X)^\beta\big),\qquad
 H(X)=\sqrt X\,h(X).
\tag{1}
\]
For \(\sigma\in\{-1,+1\}\), write
\[
 T_\sigma(X)=\{n\in\mathbb N:X<n\le X+H(X),\ \mu(n)=\sigma\}.
\tag{2}
\]
Then for every fixed \(C>0\),
\[
 \#T_\sigma(X)\ge C\,\frac{H(X)}{\log X}
\tag{3}
\]
for both signs and all sufficiently large \(X\), with the threshold depending on
\(C,\beta\).

More precisely, for every fixed positive integer \(K\), `(3)` holds with
\(C=cK\), where \(c>0\) is absolute.  Every target counted by this construction has a
canonical factorization
\[
 n=ap,\qquad p>\sqrt X>a,\qquad \mu(a)=-\sigma,
\tag{4}
\]
and the marker prime \(p\) uniquely determines \(a\).  Thus the count is a count of
distinct physical integers, not of representations.

As a consequence, after increasing the fixed \(K\), every interval
\((X,X+H(X)]\) contains at least as many positive-Möbius targets as source primes.
Partitioning a dyadic shell into such intervals gives an injection from its source primes
to positive-Möbius integers at displacement at most \(H(X)=X^{1/2+o(1)}\).  Its normalized
first-order Gibbs cost is
\[
 \ll \frac{H(X)}{\log X}=X^{1/2+o(1)}.
\tag{5}
\]
This closes `MOBIUS-PRIME-ANCHOR-PHYSICAL-HALL`.  It does not by itself cover the
positive-density composite source sector or prove `OPEN-SOURCE-001`.

## Analytic inputs

Menon's Theorem 1.1, whose paper states that the Möbius analogue is identical, gives
uniformly for \(10\le L\le Y\)
\[
 \frac1Y\int_Y^{2Y}
 \left|
   \frac1L\sum_{x<n\le x+L}\mu(n)
 \right|^2dx
 \ll
 \frac{(\log\log L)^2}{(\log L)^2}
 +\frac{(\log\log Y)^4}{(\log Y)^2}.
\tag{6}
\]
We also use the prime number theorem on fixed dyadic intervals and
\[
 \mu^2(n)=\sum_{d^2\mid n}\mu(d),\qquad
 D:=\sum_{d\ge1}\frac{\mu(d)}{d^2}=\frac6{\pi^2}.
\tag{7}
\]

For \(L=\exp((\log Y)^\beta)/O_K(1)\), `(6)` has right-hand side
\[
 R(Y,L)
 \ll_K
 \frac{(\log\log Y)^2}{(\log Y)^{2\beta}}
 +\frac{(\log\log Y)^4}{(\log Y)^2}
 =o\!\left(\frac1{\log Y}\right),
\tag{8}
\]
because \(2\beta>1\).

## Proof

### 1. Almost every cofactor interval contains linearly many of both signs

For an integer start \(t\), put
\[
 M(t,L)=\sum_{t<n\le t+L}\mu(n),\qquad
 Q(t,L)=\sum_{t<n\le t+L}\mu^2(n).
\tag{9}
\]
If \(x\in[t,t+1)\), the continuous-start sum in `(6)` differs from \(M(t,L)\)
by at most two endpoint terms.  Markov's inequality and `(8)` therefore show that,
in any fixed dyadic interval of starts of scale \(Y\),
\[
 \#\{t:|M(t,L)|>\tfrac18DL\}=o(Y/\log Y).
\tag{10}
\]

The corresponding squarefree assertion is elementary and needs no short-interval
prime theorem.  Let \(R=\lfloor\sqrt L\rfloor\) and truncate `(7)`:
\[
 Q_R(t,L)
 :=\sum_{t<n\le t+L}\sum_{\substack{d^2\mid n\\d\le R}}\mu(d)
 =DL+O(\sqrt L)
\tag{11}
\]
uniformly in \(t\).  Indeed, each \(d\le R\) contributes \(L/d^2+O(1)\),
and both the truncation tail in \(\sum\mu(d)/d^2\) and the accumulated integer-part
error are \(O(\sqrt L)\).

For starts \(t\asymp Y\), the average absolute omitted tail is bounded by
\[
 \begin{aligned}
 \frac1Y\sum_{t\asymp Y}|Q(t,L)-Q_R(t,L)|
 &\le
 \frac{L}{Y}
 \sum_{n\asymp Y}
 \sum_{\substack{d>R\\d^2\mid n}}1\\
 &\ll
 \frac{L}{Y}
 \sum_{R<d\ll\sqrt Y}\left(\frac{Y}{d^2}+1\right)
 \ll \sqrt L+\frac{L}{\sqrt Y}.
 \end{aligned}
\tag{12}
\]
Hence another application of Markov gives
\[
 \#\{t:Q(t,L)<\tfrac12DL\}
 \ll \frac{Y}{\sqrt L}+\sqrt Y
 =o(Y/\log Y).
\tag{13}
\]

Outside the union of `(10)` and `(13)`,
\[
 \#\{t<n\le t+L:\mu(n)=\pm1\}
 =\frac{Q(t,L)\pm M(t,L)}2
 \ge \frac{3D}{16}L.
\tag{14}
\]
The constant \(3D/16\) is inessential; only a fixed positive constant matters.

### 2. Reciprocal marker blocks

Put \(N=\sqrt X\).  Fix \(K\), and for \(1\le k\le K\) take marker primes
\[
 2^kN<p\le2^{k+1}N.
\tag{15}
\]
Define
\[
 t_p=\left\lfloor\frac Xp\right\rfloor,\qquad
 L_k=\left\lfloor\frac{h(X)}{2^{k+2}}\right\rfloor.
\tag{16}
\]
Then \(t_p\) lies in a fixed dyadic cofactor range of scale \(2^{-k}N\), and
\(\log L_k\sim(\log N)^\beta\).

Call \(p\) good if `(14)` holds on \((t_p,t_p+L_k]\).  The reciprocal map has
bounded fibres depending only on \(K\): if \(\lfloor X/p\rfloor=t\), then
\[
 \frac X{t+1}<p\le\frac Xt,
\tag{17}
\]
so the number of possible integral \(p\) is at most
\[
 \frac{X}{t(t+1)}+1\ll_K1.
\tag{18}
\]
Equations `(10)` and `(13)` therefore discard only \(o(N/\log N)\) marker
primes from each fixed block.  The prime number theorem gives
\[
 \#\{p\text{ good}:2^kN<p\le2^{k+1}N\}
 \gg_K\frac{2^kN}{\log N}.
\tag{19}
\]

For each good \(p\), choose every \(a\) such that
\[
 t_p<a\le t_p+L_k,\qquad \mu(a)=-1.
\tag{20}
\]
There are at least \((3D/16)L_k\) choices.  They produce
\[
 X<ap
\le X+pL_k
\le X+\frac12Nh(X)
 <X+H(X).
\tag{21}
\]
For fixed \(K\) and large \(X\),
\[
 a\le 2^{-k}N+o(N)<N<p.
\tag{22}
\]
Thus \(p\nmid a\), \(ap\) is squarefree, and
\[
 \mu(ap)=\mu(a)\mu(p)=+1.
\tag{23}
\]

### 3. Physical products are uniquely decoded

Suppose two constructed products agree:
\[
 ap=a'p'.
\tag{24}
\]
All cofactors satisfy \(a,a'<N\), while all markers satisfy \(p,p'>N\).
If \(p\ne p'\), primality and `(24)` force \(p\mid a'\), impossible because
\(0<a'<p\).  Hence \(p=p'\), and cancellation gives \(a=a'\).
This works across all \(k\), not merely inside one block.  No divisor-multiplicity
normalization is present.

Combining `(19)` with \(L_k\asymp_K2^{-k}h(X)\), every marker block contributes
\[
 \gg \frac{2^kN}{\log N}\,2^{-k}h(X)
 \gg \frac{H(X)}{\log X}
\tag{25}
\]
distinct positive-Möbius targets, with an absolute lower constant after \(K\) is
fixed.  The \(K\) blocks are disjoint under the unique marker decoding, so their
contributions add.  This proves `(3)` for \(\sigma=+1\).

Using \(\mu(a)=+1\) in `(20)` instead gives \(\mu(ap)=-1\), and `(14)` supplies
the same count.  This proves `(3)` for both signs.

### 4. Prime-anchor Hall and cost

Brun--Titchmarsh gives, since \(H(X)<X\),
\[
 \pi(X+H(X))-\pi(X)
 \le \frac{2H(X)}{\log H(X)}
 =\left(4+o(1)\right)\frac{H(X)}{\log X}.
\tag{26}
\]
Choose \(K\) so that the positive-target lower constant in `(25)`, summed over
the \(K\) blocks, exceeds \(5\).  Then every physical \(H(X)\)-cell contains
at least as many positive-Möbius targets as source primes.  Matching inside
disjoint cells yields a literal injection with displacement at most \(H(X)\).

On a dyadic physical shell of size \(U\), the total source-prime displacement is
\[
 \ll \frac{U}{\log U}\,H(U).
\tag{27}
\]
Multiplication by the Gibbs scale \(x\asymp U^{-1}\) gives `(5)`.

## Hostile audit

1. **No polylogarithmic prime PNT is used.**  Maier's theorem forbids that shortcut.
   Marker primes are counted only on fixed dyadic intervals by the ordinary PNT.
   Menon's theorem is applied to the dense cofactor starts.
2. **The sampled starts cannot hide in the exceptional set.**  Menon's exceptional
   count is \(o(N/\log N)\), not merely \(o(N)\), because \(\beta>1/2\).
   The reciprocal map has \(O_K(1)\) fibres.
3. **Squarefree mass is not inferred from a small Möbius sum.**  Equations
   `(11)`--`(13)` prove it independently.
4. **Representations are not counted as targets.**  The marker \(p>N>a\) is uniquely
   recoverable, so `(25)` counts physical integers.
5. **Constants are not hidden in Hall.**  Arbitrarily many fixed dyadic marker blocks
   amplify the lower constant past the fixed Brun--Titchmarsh constant.
6. **No RH-equivalent input appears.**  Menon's theorem, squarefree divisor identity,
   PNT, and Brun--Titchmarsh are unconditional.
7. **Scope is exact.**  The theorem closes prime-anchor capacity only.  It does not
   control a positive-density composite exceptional set or the sectorwise co-moving
   flux.

## Novelty audit

Searches covered combinations of:

- Möbius signs in every short interval;
- reciprocal sampling \(\lfloor X/p\rfloor\);
- prime--Möbius product signs;
- distinct positive/negative Möbius values at square-root scale;
- multiplicative-function sign-pattern and short-interval papers.

Known ingredients found:

- Matomäki--Radziwiłł: almost-all short averages and global sign changes;
- Matomäki--Teräväinen: all-interval Möbius cancellation only above exponent \(0.55\);
- Menon: the sharpened almost-all mean-square estimate `(6)`;
- Matomäki--Radziwiłł--Tao: positive lower density of fixed global sign patterns.

No source found the reciprocal-marker transfer, the arbitrary-constant distinct-target
law `(3)`, or its largest-prime Hall injection.  The defensible claim is a new synthesis
and extraction from Menon's theorem; external priority remains unverified.

## Route E effect

- **Closed:** `MOBIUS-PRIME-ANCHOR-PHYSICAL-HALL`.
- **New invariant:** reciprocal marker primes turn logarithmically small exceptional
  cofactor sets into collision-free physical Möbius targets.
- **Still open:** positive-density composite cube capacity and
  `MOBIUS-EXCEPTIONAL-CARLESON`, including co-moving seam flux.

## Log

- 2026-08-01 — theorem discovered, hostile-audited, and proved on paper.

## Lean completion programme (opened 2026-08-03)

This card shares its arithmetic skeleton with
`route-e-growing-reciprocal-marker-low-breadth-transport.md`, and the layer built for that card
covers almost all of it.  Corpus audit before starting, with the matching card equation:

| card equation | Lean declaration |
|-|-|
| `(4)` canonical factorization, unique decoding | `MobiusReciprocalMarkerPrimeCapacity.largePrimeMarker_product_injective`, `reciprocalMarker_target_sign_flip` |
| `(7)` `μ² = ∑_{d²∣n} μ(d)`, `D = 6/π²` | `Sieve/SquarefreeCount.sum_truncated_moebius_eq`, `squarefreeDensity_eq` |
| `(10)` Markov on the mean square | `MobiusReciprocalMarkerBlockCount.card_large_le_of_sum_sq_le` |
| `(11)` truncated squarefree count, uniform in `t` | `Sieve/SquarefreeCount.abs_truncated_squarefree_sub_le` |
| `(12)`–`(13)` averaged omitted tail | `Sieve/AveragedSquarefreeTail.sum_tail_divisor_count_le` |
| distinct-target count | `MobiusReciprocalMarkerBlockCount.card_markerBlockTargets` |
| window membership | `markerBlockTargets_mem_window` |
| target sign | `markerBlockTargets_sign` |
| marker discard by bad starts | `card_markers_start_mem_le` |
| prime supply on a dyadic block | `Sieve/PrimeWindow.card_bigPrimeSet_ratio_ge` |
| `(5)` first-order Gibbs cost | `MobiusWoldBreadthGibbsCost.abs_gibbsEdge_le`, `sum_abs_gibbsEdge_le` |

### The one missing elementary step landed — `Sieve/StartShift.lean`

The card's `(10)` passes from the continuous start of `(6)` to an integer start, "up to two endpoint
terms".  That comparison is now exact:

- `sum_Ioc_succ_self` : a one-step window is a singleton;
- **`sum_Ioc_succ_sub`** :
  `∑_{t+1 < n ≤ t+1+L} f(n) − ∑_{t < n ≤ t+L} f(n) = f(t+1+L) − f(t+1)` — an identity, valid for
  every `L` including `L = 0`;
- **`abs_sum_Ioc_succ_sub_le`**, `abs_sum_Ioc_moebius_succ_sub_le` : for a coefficient bounded by
  one — the Möbius function in particular — consecutive integer starts differ by at most two.

Built, wired, axiom-clean.

### What remains

`(6)` alone: Menon's 2026 mean-square theorem for Möbius in short intervals, the same cited
published input as the sibling card.  Mathlib has neither it nor the Matomäki–Radziwiłł theorem it
refines, and the corpus has no substitute — a mean-square bound of size `o(1/log Y)` at
`L = exp((log Y)^β)` is exactly the content of that theorem, so no weaker unconditional estimate
can stand in.  Every other step of this card is now an unconditional Lean theorem, and `(8)` is
pure arithmetic on the exponents once `(6)` is available.

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
