# Prime-valuation Kakutani polar third completion

- **ID:** `prime-valuation-kakutani-polar-third-completion`
- **Stage:** 2-fully-proven
- **Type:** INFINITE PRODUCT BRIDGE / RETIRED RH-ROUTE COMPONENT
- **Scientific status:** `[PAPER PROOF COMPLETE] [CORPUS COLLISION] [NOT NEW AS RH MECHANISM]`
  `[SCALAR GAP LEAN-FORMALIZED] [SOURCE DESCENT RH-EQUIVALENT] [NOT RH]`
- **Parents:**
  - `prime-sieve-wold-gamma-bv-relative-character.md`;
  - `../1-in-progress/source-effective-polar-kummer-conormal-purity.md`;
  - `../1-in-progress/source-curved-prime-torus-conormal-temperedness.md`;
  - `../1-in-progress/infinite-prime-wold-higgs-energy-purity.md`.
- **Statement:** The exact Wold/BV valuation-layer masses define a critical product probability
  sector over all prime valuations.  Unitary prime phases label honest polar fibres.  A coherent
  radial power twist \(p^c\) is locally normalizable throughout the zeta strip, but Kakutani's
  theorem makes its all-prime product sector equivalent to the critical sector only for \(c=0\).
  This gives a concrete Hausdorff sector model separating every off-critical coherent radial ray,
  but it does not construct the source-normal conormal boundary. The same geometric
  prime-occupation law and failed zero-to-sector descent were already isolated in the retired
  prime-aperture route.

## 1. Source-derived valuation cylinder law

For a prime \(p\), let
\[
 D_pS_p=I,\qquad E_p=I-S_pD_p
\]
be coefficient decimation, inflation, and the off-\(p\)-multiple projection.  For \(k\geq0\), put
\[
 F_{p,k}=S_p^kE_pD_p^k.                                      \tag{1}
\]
On coefficient sequences, \(F_{p,k}\) is the coordinate projection onto integers with
\(p\)-adic valuation exactly \(k\).  The projections for distinct primes commute.

Let \(Qe_n=n^{-1}e_n\) on \(\ell^2(\mathbb N_{>0})\).  The coefficient of the logarithmically
divergent first trace of \(F_{p,k}Q\) is
\[
 \mu_p(k)=(1-p^{-1})p^{-k}.                                  \tag{2}
\]
Indeed, multiplication by \(p^k\) contributes \(p^{-k}\), while exclusion of one further factor
of \(p\) contributes \(1-p^{-1}\).

The same coefficient is read by the BV/co-Poisson principal conormal.  If \(J(p_a)\) is the
pole-cancelled normal class of a scaled BV prime--polar source, the Wold renewal law gives
\[
 J(F_{p,k}p_a)
 =
 (1-p^{-1})p^{-k}J(p_a).                                    \tag{3}
\]
For a finite prime set \(P\) and a valuation packet
\(\mathbf k=(k_p)_{p\in P}\), commuting the projections in `(1)` gives
\[
 \boxed{\quad
 J\left(\prod_{p\in P}F_{p,k_p}\,p_a\right)
 =
 \left(
  \prod_{p\in P}(1-p^{-1})p^{-k_p}
 \right)J(p_a).
 \quad}                                                       \tag{4}
\]
The identical product is the singular trace density of
\(\prod_{p\in P}F_{p,k_p}Q\).  Thus `(4)` is not a probability law fitted to the divisor: it is
the common finite-dimensional distribution forced by the literal multiplication Wold tower and
the BV principal conormal before zero specialization.

Since
\[
 \sum_{k\geq0}(1-p^{-1})p^{-k}=1,
\]
Kolmogorov extension gives the product probability space
\[
 \Omega=\prod_p\mathbb N_0,\qquad
 \mu_0=\bigotimes_p\mu_p,\qquad
 \mu_p(k)=(1-p^{-1})p^{-k}.                                \tag{5}
\]
Its cylinder probabilities are exactly `(4)`.

## 2. The zero-measure boundary and its normal blow-up

For a finite set \(P\), let
\[
 A_P=\{\mathbf k\in\Omega:k_p=0\text{ for every }p\in P\}.
\]
Then
\[
 \mu_0(A_P)=a_P=\prod_{p\in P}(1-p^{-1}).                    \tag{6}
\]
As \(P\) exhausts the primes, \(a_P\to0\).  The intersection
\[
 A_\infty=\{\mathbf0\}
\]
is a source-distinguished but \(\mu_0\)-null boundary point.

Conditioning on \(A_P\) gives
\[
 \mu_0(\,\cdot\mid A_P)
 =
 \bigotimes_{p\in P}\delta_0
 \otimes
 \bigotimes_{p\notin P}\mu_p.                               \tag{7}
\]
On cylinder functions, the measures in `(7)` converge to
\(\delta_{\mathbf0}\).  This is the probability realization of the operator/conormal fracture:

- the unspecialized critical product sector is \((\Omega,\mu_0)\);
- the coarse all-prime sieve loses the conormal because `(6)` tends to zero;
- division by the exact source mass \(a_P\) is conditional normalization;
- the source-normal blow-up retains the atomic boundary state
  \(\delta_{\mathbf0}\).

The construction is Hausdorff and presentation-independent at the level of finite-dimensional
distributions.  Prime order affects a telescoping path through finite packets but not the product
measure `(5)` or the conditioned endpoint `(7)`.

## 3. Polar radial twists

Let \(\eta=(\eta_p)_p\), with \(|\eta_p|=1\), be an arbitrary unitary prime character.  It labels
the phase fibre.  Unit phases do not change the valuation probabilities and are therefore kept as
a separate character coordinate.

For \(c<\tfrac12\), twist the local orbit amplitude at valuation \(k\) by
\[
 \eta_p^k p^{ck}.
\]
After squared-norm normalization, the radial probability law becomes
\[
 \mu_{p,c}(k)
 =
 (1-p^{-(1-2c)})p^{-(1-2c)k}.                              \tag{8}
\]
Write
\[
 \mu_c=\bigotimes_p\mu_{p,c}.                               \tag{9}
\]
For a nontrivial zeta zero \(\rho\), the centered radial exponent is
\[
 c=\frac12-\operatorname{Re}\rho\in(-\tfrac12,\tfrac12),
\]
so every local law `(8)` is well-defined.  The obstruction is genuinely all-prime, not local.

## 4. Kakutani radial-sector theorem

`[PROVED HERE] [PRIME_VALUATION_KAKUTANI_RADIAL_PURITY]`

For every \(c<\tfrac12\),
\[
 \boxed{\quad
 \mu_c\sim\mu_0
 \quad\Longleftrightarrow\quad
 c=0.
 \quad}                                                       \tag{10}
\]
For \(c\neq0\), the two product measures are mutually singular.

### Proof

Put
\[
 a=p^{-1},\qquad b=p^{-(1-2c)}.
\]
The Hellinger affinity of the two local geometric laws is
\[
 H_p(c)
 =
 \sum_{k\geq0}\sqrt{\mu_{p,0}(k)\mu_{p,c}(k)}
 =
 \frac{\sqrt{(1-a)(1-b)}}{1-\sqrt{ab}}.                      \tag{11}
\]
Kakutani's product-measure theorem says that \(\mu_c\) and \(\mu_0\) are equivalent exactly when
\(\prod_pH_p(c)>0\), or equivalently when
\(\sum_p(1-H_p(c))<\infty\).

Rationalizing `(11)` gives the exact identity
\[
 1-H_p(c)
 =
 \frac{(\sqrt a-\sqrt b)^2}
 {(1-\sqrt{ab})
  \left((1-\sqrt{ab})+\sqrt{(1-a)(1-b)}\right)}.               \tag{12}
\]
The denominator in `(12)` is at most \(2\), hence
\[
 1-H_p(c)\geq\frac12(\sqrt a-\sqrt b)^2.                       \tag{13}
\]

If \(0<c<\tfrac12\), then \(b/a=p^{2c}\to\infty\).  For all sufficiently large primes,
\[
 (\sqrt a-\sqrt b)^2\geq\frac14b
 =\frac14p^{-(1-2c)}.
\]
This prime series diverges because its terms dominate a positive constant multiple of \(p^{-1}\).

If \(c<0\), then \(b/a=p^{2c}\to0\), and for all sufficiently large primes,
\[
 (\sqrt a-\sqrt b)^2\geq\frac14a=\frac1{4p}.
\]
Euler's theorem \(\sum_pp^{-1}=\infty\) again makes the Kakutani sum diverge.  Therefore
\(\mu_c\perp\mu_0\) for every \(c\neq0\).  For \(c=0\), the local laws agree identically, proving
`(10)`.

### Corpus collision and formal scalar core

The scalar numerator in `(12)` is not a new summability law.  It is exactly a reparameterized
member of the corpus prime-clock reflection hierarchy:
\[
\begin{aligned}
 G_c(p)
  &:=
  \left(p^{-1/2}-p^{-(1/2-c)}\right)^2\\
  &=
  p^c\left(
    p^{-(1+c)/2}-p^{-(1-(1+c)/2)}
  \right)^2\\
  &=
  \operatorname{weightedPrimeClockReflectionLogMomentEnergy}
  \left(0,-c,\frac{1+c}{2};p\right).                         \tag{13a}
\end{aligned}
\]
The formal damping-aperture theorem says that the last prime family is summable exactly when
\[
 \frac{1+c}{2}=\frac12
 \quad\text{or}\quad
 \left|2\frac{1+c}{2}-1\right|<-c.
\]
The second alternative is \(|c|<-c\), which is impossible, while the first is \(c=0\).  Hence
\[
 \sum_pG_c(p)<\infty\quad\Longleftrightarrow\quad c=0.        \tag{13b}
\]
This identity and `(13b)` are formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/PrimeValuationKakutaniRadialPurity.lean`.
Consequently, novelty is not claimed for the scalar divergence selector.  The candidate-new
content is the source-derived valuation-sector interpretation, the boundary blow-up, and the
still-open Xi source-normal comparison.

## 5. The third completion

Define the **prime-valuation polar sector space** to consist of:

1. the unitary character base
   \(\check X_{\rm unit}=\prod_pS^1\), retained as actual phase labels;
2. over each \(\eta\), the critical product-measure GNS sector of `(5)`;
3. its cylinder test algebra and distribution dual, which retain finite valuation jets;
4. the source-normal boundary blow-up `(7)`, which retains the normalized BV principal conormal;
5. only radial twists normal to the critical product sector.

This is deliberately a field of sectors rather than one scalar \(L^2\) space.  Distinct unitary
phases may define disjoint infinite product states and are not identified; they remain actual
fibres.  The radial question is asked relative to the sector with the same phase label.  Equation
`(10)` then says that its normal radial locus is exactly
\[
 \check X_{\rm unit}\times\{0\}.                              \tag{14}
\]

### Terminal corpus audit

With \(c=\tfrac12-\sigma\), the local law `(8)` is
\[
 \mu_{p,c}(k)=(1-p^{-2\sigma})p^{-2\sigma k},
\]
exactly the normalized prime-occupation law of
`docs/drafts/pipeline/5-failed/prime-aperture-unitary-screen-conjecture.md`.
That route already proved that the critical product sector and its Kakutani wall do not transport
analytic zeros into the wall. Helson phase twists have the same occupation probabilities while
admitting prescribed continued zeros, and desired zero-to-sector descent was proved RH-equivalent.

Wold/BV derivation of the same law and boundary-conditioning interpretation remain useful source
bridges. They do not make the product sector a new RH mechanism. The route may be reused only after
an independent source-to-conormal lift is supplied. The existing
`../1-in-progress/xi-entire-high-shell-bipolar-completion-graph.md` provides such a lift and proves
the same reflection-rate reporter, but still lacks a source operator forcing neutral rate.

This completion has the capabilities missing from the two earlier limits:

```text
finite truncations:
  retain point evaluation, lose cofinal covariance;

bare adelic/Hilbert L2:
  restore covariance, dissolve divisor fibres;

prime-valuation polar sectors:
  retain phase fibres and normalized conormal boundary,
  implement Wold prime shifts as partial isometries,
  separate every coherent nonzero radial power by measure class.
```

The strict mixed Kummer selector and `(10)` are two different radial realizations of the same
infinite obstruction.  Kummer \(L^1\) sees escape of finite-place mass to prime infinity.
Kakutani sees the corresponding coherent radial twist leave the critical product-measure sector.

Multiplicity jets do not change `(10)`: they are polynomial/distributional refinements of the
same semisimple prime character.  They belong in the cylinder-distribution dual and retain the
same radial measure class.

## 6. Exact RH consumer and remaining source theorem

Let \(N_\Xi^{\rm src}\) be the distinguished BV/co-Poisson principal conormal constructed before
choosing a zero.  The remaining theorem is no longer “find some third completion.”

> **[CONJECTURE -- XI CONORMAL CRITICAL-SECTOR NORMALITY.]**
> The normalized source-normal class `(21)` of
> `prime-sieve-wold-gamma-bv-relative-character.md`, with all multiplicity jets, has a
> source-generated polar realization in the prime-valuation sector field such that every divisor
> fibre at \(\rho\):
>
> 1. is nonzero in the cylinder-distribution dual;
> 2. has phase label \(p^{-i\operatorname{Im}\rho}\);
> 3. has radial orbit amplitude \(p^{(1/2-\operatorname{Re}\rho)k}\) on the \(p\)-valuation layer
>    \(k\);
> 4. is normal to the critical product sector over that phase label;
> 5. is produced before divisor specialization and is independent of BV window, finite-prime
>    order, and co-Poisson presentation.

The algebraic identities `(3)`--`(4)` prove the source cylinder coefficients, and BV continuation
proves the character in item 3.  What remains open is item 4: normality of the completed analytic
principal conormal rather than merely its algebraic cylinder orbit.

If the conjecture holds, apply `(10)` with
\(c=\tfrac12-\operatorname{Re}\rho\).  Normality forces \(c=0\), hence every nontrivial zero has
real part \(\tfrac12\), proving RH.

This is not a disguised local boundedness assumption.  Every finite packet and every individual
prime twist is normalizable.  Failure occurs only through the all-prime Kakutani sum.  Nor does
positive generalized-prime density, functional equation, entire completion, hypertranscendence,
or Julia orientation supply item 4: the theorem uses the literal ordinary-prime valuation product
law `(4)` and source-normal BV class.

## 7. Hostile limits

1. **Normality is load-bearing.**  Algebraic conormal survival does not imply normality in a GNS
   sector.  Assuming item 4 fibrewise is an RH-equivalent completion claim.
2. **One reference Hilbert space is too small.**  Arbitrary unitary phase characters can be
   mutually disjoint as infinite product states.  They must be retained as separate phase fibres,
   not required to be vectors in one vacuum representation.
3. **The diagonal valuation law is not the whole source.**  A generalized-prime model could copy
   a product measure.  The comparison must also preserve the actual BV/co-Poisson section,
   Gamma determinant layer, reflection, and integral ordinary-prime action.
4. **Conditioning is singular.**  The boundary state `(7)` is not obtained by ordinary
   \(L^2(\mu_0)\) projection onto \(A_\infty\), which has measure zero.  The normal blow-up is
   essential.
5. **No positivity conclusion is inferred from Kakutani alone.**  Equation `(10)` is a sector
   selector.  The frontier theorem is source-generated normality of every Xi conormal fibre.

## Novelty and literature boundary

Parent mathematics includes:

- Kakutani's equivalence/singularity theorem for product measures;
- independent geometric prime-valuation laws for zeta distributions;
- Bost--Connes/KMS product-measure and semigroup constructions;
- infinite tensor-product/GNS sector theory;
- the corpus Wold/BV renewal and conormal identities.

Targeted searches found those components but did not locate the exact source-specific theorem:
the critical \(\beta=1\) prime-valuation cylinder law simultaneously equals the multiplication-Wold
first-trace density and the BV principal-conormal renewal; its zero-measure vacuum conditioning is
the source-normal conormal blow-up; and a centered power twist is Kakutani-equivalent precisely on
the critical line.  Novelty is provisional and restricted to this conjunction and its proposed
source comparison.

Primary parents include:

- Shizuo Kakutani, *On equivalence of infinite product measures*, Annals of Mathematics 49
  (1948), 214--224;
- Jean-Benoît Bost and Alain Connes, *Hecke algebras, type III factors and phase transitions with
  spontaneous symmetry breaking in number theory*, Selecta Mathematica 1 (1995), 411--457;
- Sergey Neshveyev, *KMS states on the \(C^*\)-algebras of non-principal groupoids*,
  Journal of Operator Theory 70 (2013), 513--530.

## Gates

- [x] exact finite valuation cylinder coefficients proved
- [x] Wold first-trace and BV principal-conormal readings identified
- [x] critical product probability sector constructed
- [x] zero-measure boundary conditioning identified with source-normal blow-up
- [x] exact Hellinger affinity computed
- [x] coherent radial Kakutani purity proved
- [x] scalar Hellinger-numerator radial purity formalized in Lean
- [x] unitary phase and radial measure-class channels separated
- [x] hostile limitations stated
- [x] collision with retired prime-occupation screen recorded
- [ ] independent specialist novelty audit
- [ ] full product-measure/Kakutani formalization
- [ ] Xi conormal critical-sector normality
- [ ] RH

## Log

- 2026-07-29 — Promoted the finite-variation prime sieve to its canonical infinite product
  valuation sector.  Proved that every nonzero coherent radial exponent leaves the critical
  sector by Kakutani singularity, while arbitrary unitary phase remains a separate actual fibre.
  Identified source-normality of the normalized BV principal conormal as the single remaining
  RH-bearing comparison.
- 2026-07-29 — Hostile corpus audit found that the Hellinger numerator is exactly the existing
  damped prime-clock reflection energy at
  \((m,\theta,\sigma)=(0,-c,(1+c)/2)\).  Lean formalized the identity and its exact
  summability locus \(c=0\).  Restricted novelty claim to the valuation-sector/source-normal
  conjunction rather than the scalar selector.
- 2026-07-29 — Deeper corpus audit identified the entire geometric law with normalized
  prime-occupation law of the retired prime-aperture screen under
  \(c=\tfrac12-\sigma\). Zero-to-sector/source-normal descent is RH-equivalent, so this card is
  retained only as a Wold/BV source bridge, not as a new RH mechanism.
