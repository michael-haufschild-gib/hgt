# Primitive–fibre modular renormalization law

- **ID:** `primitive-fibre-modular-renormalization-law`
- **Stage:** 3-formalized
- **Type:** universal source law / exact RH-frontier classification
- **Status:** `[PROVED HERE] [NO RH ASSUMPTION] [NO COMPUTATION]`
- **Novelty:** `[CORPUS-NEW EXACT CROSS-FACTORIZATION] [EXTERNAL PRIORITY UNVERIFIED]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/PrimitiveFibreModularRenormalizationLaw.lean`

## Result

Fix (0<r<1), a logarithmic primitive weight (ell>0), and valuation depth
(ege0).  Put (q=r^2).  Define

\[
\begin{aligned}
 M_e(r)&=\frac{(1-r^2)(r^2)^{e+1}}{1+r^2},\\
 d(r)&=\frac r{1+r^2},\\
 G_e(r)&=r(1-r^2)(r^2)^e,\\
 J_e(r)&=\ell r^{e+1},\\
 P_e(r)&=\frac{\ell}{1-r^2}r^{-e}.
\end{aligned}
\tag{1}
\]

Then

\[
 \boxed{M_e(r)=d(r)G_e(r),\qquad J_e(r)=P_e(r)G_e(r).}
\tag{2}
\]

The first factor is occupancy Fisher damping.  The second is an independent primitive-depth
promotion, and

\[
 P_e(r)\longrightarrow+\infty.
\tag{3}
\]

For a centered modular rate (ain\mathbb R), define

\[
 T_{a,e}(r)=\exp(2a(e+1)\log r),\qquad
 J_{a,e}(r)=J_e(r)T_{a,e}(r).
\tag{4}
\]

Reflection sends (a) to (-a).  At every depth,

\[
 \boxed{J_{a,e}(r)J_{-a,e}(r)=J_e(r)^2,}
\tag{5}
\]

and

\[
 \boxed{J_{a,e}(r)=J_{-a,e}(r)\iff a=0.}
\tag{6}
\]

The exact reflected sewing cost is

\[
 \frac{J_{-a,e}(r)}{J_{a,e}(r)}
 =\exp(-4a(e+1)\log r).
\tag{7}
\]

If (a\ne0), one of `(7)` or its reciprocal tends to (+\infty) exponentially with depth.
Thus no uniformly bounded two-way depth-preserving sewing exists off the balanced half-density.

## Prime specialization

For a rational prime (p), take

\[
 r=p^{-1/2},\qquad \ell=\log p,\qquad k=e+1.
\tag{8}
\]

Then the four profiles in `(1)` are not analogies.  They are the literal corpus objects:

\[
\begin{aligned}
 M_e(p)
   &=\frac{(1-p^{-1})p^{-(e+1)}}{1+p^{-1}},
   &&\text{positive diagonal-activation mass},\\
 d(p)
   &=\frac{p^{-1/2}}{1+p^{-1}},
   &&\text{square root of occupancy Fisher information},\\
 G_e(p)
   &=(1-p^{-1})p^{-e-1/2},
   &&\text{half-shifted Gamma valuation coordinate},\\
 J_e(p)
   &=(\log p)p^{-(e+1)/2}
    =\frac{\Lambda(p^{e+1})}{\sqrt{p^{e+1}}},
   &&\text{critical primitive current}.
\end{aligned}
\tag{9}
\]

Consequently

\[
 \boxed{
 \frac{\Lambda(p^{e+1})}{\sqrt{p^{e+1}}}
 =\frac{\log p}{1-p^{-1}}p^{e/2}G_e(p).
 }
\tag{10}
\]

The direct activation-to-current gauge is

\[
 \boxed{
 \frac{J_e(p)}{M_e(p)}
 = (\log p)\frac{p+1}{p-1}p^{(e+1)/2}.
 }
\tag{11}
\]

Equation `(10)` is the missing distinction in earlier source models.  Prime powers are composite
along the local valuation fibre, but they are primitive along the Euler logarithmic derivative:
every (p^k) lies in Wold normal codimension one and carries the same primitive coefficient
(\log p), while half-density retains the depth through (p^{-k/2}).

For a general exponent (sigma=1/2+a), write

\[
 J_\sigma(p^k)=(\log p)p^{-k\sigma}.
\tag{12}
\]

Then `(5)`–`(7)` become

\[
 J_\sigma(p^k)J_{1-\sigma}(p^k)=J_{1/2}(p^k)^2,
 \qquad
 \frac{J_{1-\sigma}(p^k)}{J_\sigma(p^k)}
 =p^{k(2\sigma-1)}.
\tag{13}
\]

The half-density is therefore the unique reflection-balanced primitive current.

## Proof

The first identity in `(2)` is

\[
 \frac r{1+r^2}\,r(1-r^2)(r^2)^e
 =\frac{(1-r^2)(r^2)^{e+1}}{1+r^2}.
\]

For the second,

\[
 \frac{\ell}{1-r^2}r^{-e}\,r(1-r^2)(r^2)^e
 =\ell r^{e+1}.
\]

Since (r^{-1}>1), `(3)` follows from geometric growth.

Equations `(5)` and `(7)` follow from

\[
 T_{a,e}(r)T_{-a,e}(r)=1,
 \qquad
 \frac{T_{-a,e}(r)}{T_{a,e}(r)}
 =\exp(-4a(e+1)\log r).
\]

If (J_{a,e}=J_{-a,e}), positivity of (ell) and (r) allows cancellation of (J_e).
Injectivity of the real exponential gives

\[
 2a(e+1)\log r=-2a(e+1)\log r.
\]

Because (e+1>0) and (log r<0), this is equivalent to (a=0), proving `(6)`.  If
(a>0), the base (exp(-4a\log r)) in `(7)` exceeds one, so `(7)` tends to infinity.  If
(a<0), apply the same argument to (-a).

For `(9)`, the exact diagonal-activation law gives the first line, the existing Fisher identity
gives the second, and the half-shifted valuation definition gives the third.  The prime-power
identity

\[
 \Lambda(p^{e+1})=\log p
\]

gives the fourth.  Substitution proves `(10)`–`(13)`.

## Corpus-wide consequences

This law changes the current frontier classification.

1. **Activation/Möbius/Gamma.** Möbius depth differences are joint positive-valuation
   probabilities.  Fisher whitening recovers (G_e), not (J_e).  The old “Gamma recovery
   gauge” accounts only for rare-prime occupancy; it misses the independent depth promotion
   (p^{e/2}).
2. **Wold.** The first normal jet selects (omega(n)=1), hence every prime power.  Its primitive
   coefficient is (Lambda).  Valuation depth and Wold codimension are independent source axes,
   not competing descriptions of one filtration.
3. **Julia/KMS and CCM.** Inverse FDT reconstructs the literal half-density current and Julia
   resolves it into positive scale layers.  Since every layer remains diagonal in the prime-power
   label, this resolution cannot change a negative first-clock phase.
4. **Reflection and Schatten duality.** The two reflected exponent sectors have fixed product
   density and Hölder-conjugate critical ideals.  Equality occurs only at exponent (1/2); ordinary
   trace pairing remains on the divergent prime-harmonic boundary.
5. **Rees and source modular no-sewing.** Off-center reflection requires an exponential depth
   gauge.  Finite-Rees and bounded graded operators cannot supply it.  Even at the balanced point,
   valuation-to-primitive promotion is unbounded, so “put the Gamma frame in a better Hilbert
   space” does not create the critical current.
6. **Sonin/Calkin and Ward.** Their literal prime-power coefficients are consumers of (J_e), not
   of (M_e) or (G_e).  Compression or positivity after primitive promotion cannot explain how
   the promotion was obtained.
7. **Möbius frontier.** Positive one-transition renewal geometry cannot replace the signed global
   cancellation needed before primitive extraction.  Absolute values return to the occupancy
   side of `(2)` and lose the required current.

## Hostile audit

1. Geometric prime valuations, squarefree Bernoulli laws, Fisher information, the von Mangoldt
   function, Euler logarithmic derivatives, half-density, KMS identities, and functional-equation
   reflection are established parent mathematics.
2. Standalone algebra in `(2)`–`(7)` is elementary.  Candidate-new content is the exact
   identification `(9)`–`(11)` across four independently developed source constructions and the
   resulting separation of prime breadth, valuation depth, and modular reflection into three
   noninterchangeable gauges.
3. The theorem does not prove RH and supplies no one-sided sign.  It classifies the source object
   a successful proof must transport and proves sharp impossibility for bounded depth-preserving
   substitutes.
4. The theorem does not say every modular character is unitary.  It proves the exact opposite:
   within the source-pointed primitive depth representation, reflection balance occurs only at
   (a=0), while every (a\ne0) has exponentially divergent two-way sewing cost.
5. The theorem does not kill all Hilbert–Pólya, CCM, Hedenmalm, Deninger, or co-Poisson programs.
   It kills only routes that identify positive valuation completion with primitive-current
   completion or require a bounded depth-preserving reflected sewing.

## Literature boundary

Targeted searches found the parent theories separately: independent geometric prime valuations and
squarefree reciprocal laws; Euler logarithmic derivatives and von Mangoldt prime-power support;
half-density in explicit-formula operator models; KMS/detailed balance; and Schatten/Hölder
duality.  No located source states the exact activation–Fisher–Gamma–primitive factorization
`(9)`–`(11)` or uses it to classify reflected depth sewing.  This is noncollision evidence, not a
priority certificate.

## Gates

- [x] dependency-closed paper proof
- [x] exact prime specialization
- [x] reflection balance classification
- [x] depth-divergence theorem
- [x] preliminary corpus and literature collision audit
- [x] Lean formalization
- [ ] independent specialist priority review

