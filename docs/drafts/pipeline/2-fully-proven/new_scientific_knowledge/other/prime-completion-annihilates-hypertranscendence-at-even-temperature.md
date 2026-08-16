# Prime completion can annihilate hypertranscendence while preserving every Euler boundary jet

- **ID:** `prime-completion-annihilates-hypertranscendence-at-even-temperature`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / SOURCE-PURE HT-TO-DA COMPLETION / EMERGENT-SYMMETRY LAW
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[EXTERNAL EXACT-MATCH SEARCH NEGATIVE] [NOT AN RH RESULT]`
- **Sources:** `../../../3-formalized/summable-nome-infinite-order-multiple-elliptic-gamma.md`;
  `../../4-publication-ready/multiple-elliptic-gamma-rational-rank-dichotomy/main.tex`
- **Statement:** Every finite prime packet with at least two primes produces a
  hypertranscendental multiple-\(q\)-Pochhammer function.  At every even integer temperature,
  the cofinal all-prime completion is nevertheless differentially algebraic.  Its complete
  logarithmic normal jet is the genuine Riemann-zeta dilation tower.

## Why this is the active theorem

The first attempted Xi sewing specialized a multiple-\(q\) product diagonally and thereby added
partition multiplicities not present in one local Euler ray.  Projecting to one fugacity particle
recovered the Euler factor but discarded the full hypertranscendental function.

The construction below is different.  It uses all occupation modes of a finite prime packet.  By
unique factorization, cofinal prime completion identifies those modes with all positive integers.
No Möbius dequantization, analytic continuation, zero set, or Xi input is used.  Every finite Euler
packet occurs as an actual normal derivative, and every higher logarithmic normal derivative also
has an exact arithmetic meaning.

## Exact theorem

Fix an integer \(r\ge 2\).  For a finite set \(S\) of rational primes, put

\[
 q_p=p^{-r},\qquad
 \tau_p=\frac{ir\log p}{2\pi},
 \qquad
 \Phi_{S,r}(x)
   =\prod_{\nu\in\mathbb N^S}
      \left(1-x\prod_{p\in S}p^{-r\nu_p}\right).                 \tag{1}
\]

The product is entire in \(x\).  If \(|S|\ge2\), then

\[
 z\longmapsto \Phi_{S,r}(e^{2\pi iz})
 \quad\text{is hypertranscendental over }\mathbb C(z),          \tag{2}
\]

and \(\Phi_{S,r}(x)\) is hypertranscendental over \(\mathbb C(x)\).

As \(S\) tends through the directed set of finite prime subsets,

\[
 \Phi_{S,r}(x)\longrightarrow
 \Phi_{\infty,r}(x):=\prod_{n\ge1}\left(1-\frac{x}{n^r}\right)  \tag{3}
\]

normally on \(\mathbb C\).  On \(|x|<1\),

\[
 \log\Phi_{S,r}(x)
   =-\sum_{m\ge1}\frac{x^m}{m}
      \prod_{p\in S}(1-p^{-rm})^{-1},                           \tag{4}
\]

and hence every logarithmic normal coefficient converges:

\[
 [x^m]\log\Phi_{S,r}(x)
   \longrightarrow-\frac{\zeta(rm)}m.                          \tag{5}
\]

In particular,

\[
 \Phi_{S,r}'(0)
   =-\prod_{p\in S}(1-p^{-r})^{-1}
   \longrightarrow-\zeta(r).                                  \tag{6}
\]

If \(r=2k\) is even, then the all-prime limit is differentially algebraic over
\(\mathbb C(x)\).  More explicitly, if \(t^r=x\) and
\(\omega=e^{2\pi i/r}\), then

\[
 \Phi_{\infty,r}(x)
   =\prod_{j=0}^{k-1}
      \frac{\sin(\pi\omega^j t)}{\pi\omega^j t}.                \tag{7}
\]

For \(r=2\),

\[
 \Phi_{\infty,2}(x)
   =\frac{\sin(\pi\sqrt{x})}{\pi\sqrt{x}},\qquad
 4x\Phi_{\infty,2}''+6\Phi_{\infty,2}'+\pi^2\Phi_{\infty,2}=0. \tag{8}
\]

Thus a normally convergent net of named hypertranscendental functions has a
differentially algebraic limit, although its complete Euler boundary jet converges coefficient by
coefficient to the actual zeta tower \((\zeta(rm))_{m\ge1}\).

## Paper proof

### 1. Rational rank of every finite prime packet

For distinct primes \(p,q\), suppose

\[
 a+b\tau_p+c\tau_q=0,\qquad a,b,c\in\mathbb Q.
\]

The real part gives \(a=0\).  The imaginary part gives

\[
 b\log p+c\log q=0.
\]

After clearing denominators and exponentiating, unique factorization gives
\(p^Bq^C=1\), hence \(B=C=0\) and then \(b=c=0\).  Therefore

\[
 \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
    \{1,\tau_p:p\in S\}\ge3                                  \tag{9}
\]

whenever \(|S|\ge2\).

### 2. The backward multiple-\(q\) product is hypertranscendental

Let

\[
 B_S(z)=\Phi_{S,r}(e^{2\pi iz})
\]

and let \(F_S\) be the forward factor in the parity-correct multiple elliptic Gamma product.
Writing \(T_S=\sum_{p\in S}\tau_p\), the defining products give

\[
 F_S(z)=B_S(T_S-z).                                          \tag{10}
\]

The exact period-rank dichotomy and `(9)` say that the full multiple elliptic Gamma function

\[
 G_S=
 \begin{cases}
 F_S/B_S,&|S|\text{ even},\\
 F_SB_S,&|S|\text{ odd}
 \end{cases}
\]

is hypertranscendental over \(\mathbb C(z)\).

If \(B_S\) were differentially algebraic, then \(B_S(T_S-z)\) would be differentially
algebraic: affine reflection replaces the \(j\)-th derivative by \((-1)^j\) times the reflected
derivative and preserves \(\mathbb C(z)\).  Differentially algebraic meromorphic functions form a
field, so \(G_S\) would be differentially algebraic.  This contradicts the rank theorem and proves
`(2)`.

To pass from \(z\) to \(x\), suppose instead that \(\Phi_{S,r}\) were differentially algebraic over
\(\mathbb C(x)\).  With \(\delta=x\,d/dx\), the packets

\[
 (\Phi,\Phi',\ldots,\Phi^{(n)})
 \quad\text{and}\quad
 (\Phi,\delta\Phi,\ldots,\delta^n\Phi)
\]

are related over \(\mathbb C(x)\) by invertible triangular Stirling transforms.  Hence
\(\Phi_{S,r}\) is also differentially algebraic for \(\delta\).  Under
\(x=e^{2\pi iz}\),

\[
 \frac{d^n}{dz^n}\Phi_{S,r}(e^{2\pi iz})
   =(2\pi i)^n(\delta^n\Phi_{S,r})(e^{2\pi iz}).
\]

The exponential coordinate is itself differentially algebraic over \(\mathbb C(z)\).
Differential-algebraic transitivity would make \(B_S\) differentially algebraic over
\(\mathbb C(z)\), contradicting `(2)`.  Therefore \(\Phi_{S,r}\) is hypertranscendental over
\(\mathbb C(x)\).

### 3. Prime completion and the full Euler normal jet

Unique factorization is a bijection

\[
 \mathbb N^{(\mathcal P)}\longrightarrow\mathbb N_{\ge1},
 \qquad
 \nu\longmapsto\prod_p p^{\nu_p}.                             \tag{11}
\]

Since \(r>1\),

\[
 \sum_{n\ge1}n^{-r}<\infty.
\]

The standard normal-product criterion therefore shows that the products indexed by occupations
supported in \(S\) converge, as a net, to the product indexed by all positive integers.  This
proves `(3)`.

For \(|x|<1\), absolute convergence permits logarithmic expansion and reordering:

\[
 \begin{aligned}
 \log\Phi_{S,r}(x)
 &=-\sum_{\nu\in\mathbb N^S}\sum_{m\ge1}
     \frac{x^m}{m}\prod_{p\in S}p^{-rm\nu_p}\\
 &=-\sum_{m\ge1}\frac{x^m}{m}
     \prod_{p\in S}(1-p^{-rm})^{-1}.
 \end{aligned}
\]

This is `(4)`.  The ordinary Euler product in its absolutely convergent half-plane gives `(5)`;
the case \(m=1\) gives `(6)`.

### 4. Even-temperature reflection collapse

Let \(t^r=x\) and let \(\omega\) be a primitive \(r\)-th root of unity.  The Weierstrass product
for reciprocal Gamma gives

\[
 \prod_{j=0}^{r-1}\Gamma(1-\omega^jt)^{-1}
   =\prod_{n\ge1}\prod_{j=0}^{r-1}
      \left(1-\frac{\omega^jt}{n}\right)
   =\prod_{n\ge1}\left(1-\frac{x}{n^r}\right).                \tag{12}
\]

The exponential counterterms cancel because \(\sum_j\omega^j=0\).

For \(r=2k\), pair \(j\) with \(j+k\), so that
\(\omega^{j+k}=-\omega^j\).  Euler reflection gives

\[
 \bigl(\Gamma(1-a)\Gamma(1+a)\bigr)^{-1}
   =\frac{\sin(\pi a)}{\pi a}.
\]

Multiplying the \(k\) pairs proves `(7)`.  Each factor is differentially algebraic over the
algebraic extension \(\mathbb C(t)/\mathbb C(x)\); differential-algebraic transitivity proves that
the single-valued entire product is differentially algebraic over \(\mathbb C(x)\).

At \(r=2\), Euler's sine product gives the first formula in `(8)`.  Direct differentiation gives
the displayed second-order linear equation.  This completes the proof. `QED`

## New mathematical mechanism

Every finite packet sees only multiplicative prime shifts.  Its smooth-number occupation spectrum
has no global additive successor and its period packet contains a rank-three minor, forcing the
HT phase.

Cofinal completion adds no fake coefficients: it uses unique factorization to turn the complete
prime occupation monoid into all positive integers.  The completed zero divisor therefore gains a
global arithmetic organization absent from every finite packet.  At even temperature, root pairing
and Gamma reflection convert that organization into a finite trigonometric expression.

The exact mechanism is

```text
finite independent prime periods
  -> HT multiple-q product
  -> cofinal source-pure prime completion
  -> emergent all-integer successor/reflection symmetry
  -> DA trigonometric limit,
```

while

```text
complete logarithmic normal jet
  -> finite Euler packets
  -> (zeta(r), zeta(2r), zeta(3r), ...).
```

Thus neither source purity, normal convergence, nor convergence of every boundary jet conserves
hypertranscendence.  What disappears is the finite-period differential phase, not the Euler source.

## What is parent mathematics

- unique factorization and the Euler product for \(\zeta(s)\);
- Euler's sine product, the reciprocal-Gamma Weierstrass product, and Gamma reflection;
- generating products for repeated multiple-zeta values;
- failure of differential algebraicity to be closed under locally uniform limits;
- the repository's finite period-rank dichotomy and paper-proved infinite-nome normal convergence.

The candidate-new claim is their exact source-labelled coupling: every finite prime face is
hypertranscendental, the cofinal all-prime object is DA at every even temperature, and the whole
Euler/zeta normal jet survives the phase annihilation.  Exact, stronger, equivalent, and mechanism
searches through July 2026 found the classical product identities and multiple-zeta generating
functions, but no theorem stating this finite-face HT / all-prime DA phase reversal.

Primary adjacent sources:

- NIST DLMF, Gamma reflection and reciprocal-Gamma products:
  <https://dlmf.nist.gov/5.5.E3> and <https://dlmf.nist.gov/5.8>.
- J. M. Borwein, D. M. Bradley, D. J. Broadhurst, and P. Lisonek,
  *Combinatorial aspects of multiple zeta values*,
  <https://arxiv.org/abs/math/9812020>.
- M. E. Hoffman, *On Multiple Zeta Values of Even Arguments*,
  <https://arxiv.org/abs/1205.7051>.
- A. Narukawa, *The modular properties and the integral representations of the multiple elliptic
  gamma functions*, <https://arxiv.org/abs/math/0306164>.

Independent specialist priority audit remains open.

## Hostile significance and RH audit

- **Not an RH implication.** The theorem is proved at fixed \(r>1\), with an explicit DA collapse
  at even integer \(r\).  It gives no continuation to the critical strip and no zero orientation.
- **Not a coefficient trick.** Every occupation mode is retained; no one-particle projection is
  used.  Equations `(4)`--`(6)` identify the actual source normal jet.
- **Not stability of HT.** It proves the opposite.  Any argument assuming HT survives all-prime
  completion is false even under normal convergence and full-jet convergence.
- **No contradiction with finite rank law.** The all-prime limit is a new analytic object.  The
  finite rational-rank theorem never asserted closure under infinite-nome completion.
- **No Möbius wall hidden.** The proof remains in the absolutely convergent half-plane and uses
  unique factorization directly.

The RH consequence is architectural and strict:

> A source-native HT-to-Xi bridge must transport a completion-stable polarized invariant, not
> merely differential transcendence or its complete boundary jet.

The next live question is whether the disappearing finite-face HT obstruction has a canonical
renormalized vanishing-cycle, determinant-line, or signed Pick class whose all-prime limit is
nonzero and whose reflection defect is the Xi transverse displacement.  Without such a conserved
class, attaching a hypertranscendental carrier to the Euler source does not move the Pick-kernel
open core.

## Gates

- [x] internal corpus collision search
- [x] exact finite-prime source and cofinal completion stated
- [x] dependency-closed paper proof
- [x] hostile differential-axis, completion, and RH audit
- [x] external exact/stronger/equivalent/mechanism search
- [ ] independent specialist priority audit
- [ ] 2 -> 3 formalized: unconditional Lean finite HT, prime completion, Euler jet, and DA limit
- [ ] construct a nonzero completion-stable polarized survivor
- [ ] connect that survivor to the Xi Pick-kernel domination problem

## Log

- 2026-07-27 — direct eta specialization rejected as non-source-pure; one-particle extraction
  recovered the Euler ray but discarded the HT carrier.
- 2026-07-27 — Möbius dequantization recovered the ray exactly but reduced to the existing
  RH-equivalent Möbius continuation wall.
- 2026-07-27 — replacing diagonal eta sewing by the complete prime occupation monoid produced the
  source-pure theorem above.
- 2026-07-27 — even-temperature all-prime completion identified with a finite Gamma-reflection
  product, proving actual HT-to-DA phase annihilation while all zeta normal jets survive.

## Lean status — 2026-08-16: the completion, the Euler jet, and the even-temperature collapse

`formal/GaloisForLFunctions/HTGeometry/PrimeOccupationCompletionProduct.lean`, unconditional and
axiom-clean, wired into the `HTGeometry` umbrella (with the two-product comparison added to
`HTGeometry/InfiniteProductNearOne.lean`).

**The completed product `(3)`.**  The all-prime limit is the canonical product with zeros `n^r`:

```text
occupationProduct r x := powerCanonicalProduct r (-x)
hasProd_occupationProduct :   HasProd (fun n => 1 - x/(n+1)^r) (occupationProduct r x)   (r ≥ 2)
analyticOnNhd_occupationProduct
```

**The packet product and its cofinal completion, `(3)` and `(11)`.**  Unique factorization is
already built into the index: the occupation modes supported in a prime packet are exactly the
smooth numbers of that packet, so the packet product is

```text
occSmooth N r x m         := if m ∈ Nat.smoothNumbers N then -(x/m^r) else 0
smoothOccupationProduct N r x := ∏'_m (1 + occSmooth N r x m)
tendsto_smoothOccupationProduct :
    smoothOccupationProduct N r x  →  occupationProduct r x     as N → ∞,
```

proved by the two-product estimate `‖∏(1+a) − ∏(1+b)‖ ≤ (Σ‖a−b‖)·exp(Σ(‖a‖+‖b‖))`
(`norm_tprod_one_add_sub_tprod_one_add_le`, new in `InfiniteProductNearOne.lean`) together with the
smooth-number tail estimate.  This is exactly `(3)`, with the directed set of finite prime packets
realized cofinally by the packets of primes below `N`.

**The Euler boundary jet `(4)`–`(6)`.**  The `m`-th logarithmic coefficient of the packet product is
`−1/m` times its occupation divisor sum, and that sum is the finite Euler product:

```text
natPowInvHom k                       the multiplicative weight n ↦ n^(-k)
smoothZetaSum N k                    := ∑'_{n ∈ smoothNumbers N} n^(-k)
prod_primesBelow_eq_smoothZetaSum :  ∏_{p < N}(1 - p^(-k))^(-1) = smoothZetaSum N k
tendsto_smoothZetaSum :              smoothZetaSum N k → ζ(k)
tendsto_prod_primesBelow_riemannZeta : ∏_{p<N}(1 - p^(-k))^(-1) → ζ(k)
```

At `k = r·m` this is `(5)`; at `k = r` it is `(6)`.

**Even-temperature collapse `(7)`–`(8)`.**  The corpus already owned the sine factorization of an
even-exponent canonical product, so the completed product is differentially algebraic:

```text
differentiallyAlgebraic_occupationProduct_of_even :  r ≥ 2 even ⇒ DA over ℂ(x)
occupationProduct_two_sq :        Φ₂(c²) = sincProduct c
pi_mul_occupationProduct_two :    π c · Φ₂(c²) = sin(π c)
ode_of_sin_square_law :           an entire function with that square law solves
                                    4 x y'' + 6 y' + π² y = 0
occupationProduct_two_ode :       4 x Φ₂'' + 6 Φ₂' + π² Φ₂ = 0
```

The last two are `(8)` verbatim.  The general even case `(7)` is
`differentiallyAlgebraic_occupationProduct_of_even`, which runs through the corpus's
`powerCanonicalProduct_even_eq_prod_sinc` — the `2m`-th roots of unity pairing off into `m` Euler
sine products — so the reflection collapse is machine-checked, not quoted.

**What is left.**  Item `(2)`: hypertranscendence of a finite packet.  The corpus owns the exact
input `HTGeometry.hypertranscendentalOver_multipleEllipticGammaMero_twoLogPrime` (two distinct
primes give a rank-three period minor, hence a hypertranscendental multiple elliptic Gamma carrier);
what remains is the bridge identifying `Φ_{S,r}(e^{2πiz})` with the backward factor of that carrier,
together with the affine-reflection and Stirling-transform transfers of the card's step 2.

### Item `(2)` is formalized too: every finite packet is hypertranscendental at every temperature

`formal/GaloisForLFunctions/HTGeometry/PrimePowerOccupationHypertranscendence.lean`, unconditional
and axiom-clean, wired into the `HTGeometry` umbrella.

The corpus already owned the linear-temperature case.  The step to temperature `r` is exactly the
card's `(9)`: the periods `τ_p = i r log p / (2π)` are the integer multiple `r · (i log p / 2π)` of
the reciprocal-prime periods, and scaling an integrally independent family by a nonzero integer
keeps it integrally independent.

```text
primePowerNomePeriod r q i      := r · primeNomePeriod q i
primePowerNomePeriod_im_pos
ellipticNome_primePowerNomePeriod :   nome = (1/q i)^r
periodsIntegrallyIndependent_natCast_mul
periodsIntegrallyIndependent_primePowerNomePeriod

primePowerNome r p              := (1/p)^r
primeOccupationFacePow r S      := ∏'_{ν : S →₀ ℕ} (1 - t · ∏_p (1/p)^(r ν_p))     -- this is Φ_{S,r}
multipleEllipticGammaBackwardProduct_primePowerNomePeriod :
    the backward multiple elliptic Gamma product at those periods IS Φ_{S,r}(e^{2πiz})
hypertranscendental_primeOccupationFacePow :
    r ≥ 1, |S| ≥ 2  ⇒  Φ_{S,r} is hypertranscendental
hypertranscendental_primeOccupationFacePow_neg :    the reflected face too
```

The descent from the additive variable `z` to the multiplicative variable `x` is the corpus's
`hypertranscendental_of_comp_exp`, which is exactly the card's Stirling-transform argument in
step 2.

**Unique factorization `(11)` is formalized** as an equivalence, in
`PrimeOccupationCompletionProduct.lean`:

```text
occupationEquivPrimeSupported : (Nat.Primes →₀ ℕ) ≃ {f : ℕ →₀ ℕ // support prime}
occupationEquivPNat           : (Nat.Primes →₀ ℕ) ≃ ℕ+
occupationEquivPNat_coe       : the value is the monomial ∏ p^{ν_p}
```

**What is left.**  One bookkeeping identification: transporting `primeOccupationFacePow r S`
(indexed by occupation vectors `ν : S →₀ ℕ`) to `smoothOccupationProduct N r` (indexed by the
`S`-smooth positive integers) along the restriction of `occupationEquivPNat` to a packet.  With
that one reindexing, items `(2)`, `(3)`, `(5)`, `(6)`, `(7)` and `(8)` all refer to the same
object and the card is complete.
