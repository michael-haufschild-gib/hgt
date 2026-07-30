# Positive occupancy–Möbius boundary-polarity law

Status: `[LEAN-PROVED — NOVELTY UNVERIFIED]`

## Exact claim

Fix \(K\ge 12\). Let
\[
 P_{K,N}(s)
 :=\zeta(s)\sum_{j=0}^{N}M_{K,j}(s)
 =\frac{\zeta(s)}{\zeta((K+N)s)},
\]
where \(M_{K,j}\) are the complete positive-resolution multipliers.

The proposed theorem is the following single source-to-divisor law.

1. **Positive bulk.** The channel coefficients are pairwise disjoint and lie in
   \(\{0,1\}\); their countable sum is the constant-one arithmetic function. The
   multiplier family is differentially independent over the full zeta
   differential field, and every channel carries exactly the zeta divisor on
   \(\Re s>1/2\).

2. **Scale classification.** If \(\varepsilon_n\to0\) and
   \(d_n\varepsilon_n\to\lambda\), then, away from the pole and zero set of the
   denominator,
   \[
   \frac{\zeta(\varepsilon_nu)}
        {\zeta(d_n\varepsilon_nu)}
   \longrightarrow
   \frac{\zeta(0)}{\zeta(\lambda u)}
   =-\frac1{2\zeta(\lambda u)}.
   \]
   Renormalized depth \(0\) gives the identity, finite nonzero depth retains a
   reciprocal divisor, and right-escaping depth gives the endpoint constant
   \(-1/2\).

3. **Forced sign transmutation.** For every real \(x>1\), the native values
   \(P_{K,N}(x)\) are positive. By contrast,
   \[
   P_{K,N}\!\left(\frac{x}{K+N}\right)
   \longrightarrow -\frac1{2\zeta(x)}<0,
   \]
   so the critical values are eventually negative. Their observation points
   eventually lie outside \(\Re s>1\), the common half-plane on which the
   \(0/1\) Dirichlet expansions converge. On \(\Re u>1\), the exceptional
   boundary has the expansion
   \[
     -\frac1{2\zeta(u)}
     =\sum_{n\ge1}\frac{-\mu(n)/2}{n^u},
   \]
   whose first two coefficients have opposite signs:
   \(-\mu(1)/2=-1/2<0<1/2=-\mu(2)/2\).
   Consequently this boundary cannot be a coefficientwise limit of
   nonnegative coefficients on a fixed Dirichlet basis. Retaining the divisor
   therefore forces a moving-frequency, analytically continued limit; ordinary
   positive convergence cannot produce it.

4. **Divisor polarity and minimal orientation.** At every divisor point
   \(\rho\), the exceptional reciprocal section reverses meromorphic order.
   For the completed Riemann carrier, reflection selects, up to scale, the
   unique affine odd weight \(s-\tfrac12\). Its boundary logarithmic current has
   residue
   \[
     -m_\rho\!\left(\rho-\tfrac12\right).
   \]
   Every reflection-even scalar observer is noninjective and therefore cannot
   retain this signed lateral displacement.

Thus one family exhibits a forced three-stage transmutation
\[
\boxed{\text{\(0/1\) occupancy}}
\;\xrightarrow[\text{singular moving scale}]{}
\boxed{\text{signed Möbius inversion / opposite divisor}}
\;\xrightarrow[\text{unique affine polarization}]{}
\boxed{\text{critical-line orientation}}.
\]
Fixed-scale observation loses inversion; ordinary positive convergence cannot
reach the exceptional divisor; reflection-even scalarization loses
orientation. These are not independent defects but three projections of the
same exceptional-boundary law.

## Why this would be new knowledge

The individual identities
\(\sum 1_{\text{\(m\)-free}}(n)n^{-s}=\zeta(s)/\zeta(ms)\) and
\(\sum\mu(n)n^{-s}=1/\zeta(s)\) are classical. The candidate contribution is
not either identity. It is the necessity theorem joining:

- a complete disjoint positive resolution;
- maximal relative differential-algebraic rank;
- full common divisor retention;
- classification by renormalized depth;
- unavoidable positive-to-signed transition at every divisor-retaining scale;
- reversal of divisor order; and
- uniqueness/minimality of the affine reflection polarization that preserves
  the side of the critical line.

If true and priority-surviving, it identifies Möbius inversion as the
exceptional boundary of finite positive prime occupancy and explains why
positivity, compact fixed-scale limits, and even divisor counts repeatedly fail
to orient the Riemann divisor.

## Complete paper proof

### Positive bulk

Use the existing complete-resolution coefficient partition, prefix telescope,
relative differential-independence theorem, and channel analytic-order theorem.
No new argument is needed here.

### Scale classification

For
\[
Q_d(\varepsilon u)=
\frac{\zeta(\varepsilon u)}{\zeta(d\varepsilon u)},
\]
continuity of \(\zeta\) at \(0\), continuity and nonvanishing at \(\lambda u\),
and the quotient limit theorem give
\[
Q_{d_n}(\varepsilon_nu)\to
\zeta(0)/\zeta(\lambda u).
\]
If \(d_n\varepsilon_nu\) escapes through the right half-plane, then
\(\zeta(d_n\varepsilon_nu)\to1\), giving \(\zeta(0)=-1/2\).
The fixed, critical, mesoscopic, and microscopic representatives are the
already proved specializations.

### Forced sign transmutation

Fix \(x>1\).

For every nonzero integer \(m\),
\[
P_m(x)=\sum_{n\ge1}\frac{1_{\text{\(m\)-free}}(n)}{n^x}>0
\]
because all coefficients are nonnegative and the coefficient at \(n=1\) is
one. Equivalently, both real zeta values in
\(\zeta(x)/\zeta(mx)\) are positive.

At critical scale,
\[
P_m(x/m)=\frac{\zeta(x/m)}{\zeta(x)}
\longrightarrow\frac{\zeta(0)}{\zeta(x)}
=-\frac1{2\zeta(x)}<0.
\]
Since the limit is strictly negative and real, the critical values are
eventually negative. Also \(x/m<1\) for every integer \(m>x\), so these values
are eventually outside the native Dirichlet half-plane.

For \(\Re u>1\), absolute convergence and the classical reciprocal zeta
identity give
\[
-\frac1{2\zeta(u)}
=-\frac12\sum_{n\ge1}\mu(n)n^{-u}.
\]
The identities \(\mu(1)=1\), \(\mu(2)=-1\) give the two strict coefficient
signs. If nonnegative coefficients \(a_r(n)\) converged coefficientwise to
\(-\mu(n)/2\), closedness of \([0,\infty)\) would force
\(-\mu(1)/2\ge0\), contradiction. Hence a fixed-basis coefficientwise positive
limit is impossible.

### Divisor polarity and affine orientation

For any carrier \(F\) with \(F(0)\ne0\), the exceptional section is
\(F(0)/F(u)\). Additivity of meromorphic order under quotient gives
\[
\operatorname{ord}_\rho(F(0)/F)
=-\operatorname{ord}_\rho F.
\]
If \(F(1-s)=F(s)\), its logarithmic derivative is reflection odd. An affine
weight \(as+b\) is reflection odd about \(1/2\) iff
\(b=-a/2\), hence it is \(a(s-1/2)\). The corresponding exceptional boundary
current has residue \(-m_\rho(\rho-1/2)\). Finally an even observer satisfies
\(\mathcal O(\rho)=\mathcal O(1-\rho)\), so it cannot be injective.

All proof obligations are closed on paper.

## Hostile attacks

1. **“The limit is one line.”** Correct. The limit alone is routine and is not
   the theorem. Contribution must stand or fall on forced sign transmutation,
   complete positive hypertranscendental realization, scale classification,
   divisor reversal, and polarization minimality as one necessity law.

2. **“This is decorative RH language.”** The theorem does not claim zero
   exclusion. Its RH content is exact: it identifies which operation first
   creates signed divisor information and which subsequent projection destroys
   lateral orientation. Any paper must state that this is structural progress,
   not an RH proof.

3. **“Coefficientwise impossibility is trivial.”** As an isolated lemma it is.
   Its role is to certify the nonregular nature of the explicit positive-to-
   Möbius transition. It cannot carry significance by itself.

4. **“Finite nonzero \(\lambda\), not only \(\lambda=1\), retains a divisor.”**
   Correct. The paper must state a critical *class*, parameterized by finite
   nonzero renormalized depth, not a unique critical scale.

5. **“Oscillatory renormalized depth is unclassified.”** Correct. The theorem
   classifies convergent finite depth and right-escaping depth. It must not claim
   all possible scale sequences.

6. **“The positive Dirichlet series does not converge at the critical
   points.”** This is the mechanism, not a bug. The result explicitly proves
   eventual escape from the convergence half-plane and uses analytic
   continuation.

7. **“The physics language is overreach.”** “Occupancy” refers only to bounded
   prime exponents. No quantum-statistical claim is part of the theorem.

## Preliminary novelty audit

- `[KNOWN]` \(m\)-free Dirichlet series
  \(\zeta(s)/\zeta(ms)\).
- `[KNOWN]` reciprocal-zeta Möbius Dirichlet series.
- `[KNOWN]` classical work relates \(m\)-free counting errors to zeta zeros.
- `[KNOWN]` recent work studies analytic continuation of \(m\)-free Dirichlet
  series and values such as \(\zeta(1/m)\).
- `[CORPUS]` complete positive disjoint resolution, maximal relative
  differential independence, common divisor, exact prefix telescope, scale
  transition, exceptional divisor reversal, and affine polarization.
- `[NOVELTY UNVERIFIED]` exact positive-to-Möbius sign-transmutation and
  polarity necessity law as one theorem.

Targeted searches have not yet found the inverse-depth limit interpreted as a
forced transition from positive bounded-exponent arithmetic to mixed-sign
Möbius inversion, nor its conjunction with relative hypertranscendence and
critical-line polarization. Absolute priority is not claimed.

## Formalization

Formalized in
`formal/GaloisForLFunctions/RHTower/XiSourceNormalConeDivisorConservation.lean`.

Main declaration:

- `RHTower.positiveOccupancyMobiusBoundaryPolarity_law`

Supporting declarations:

- `RHTower.LSeries_mobiusExceptionalCoefficient`;
- `RHTower.no_nonnegative_coefficients_tendsto_mobiusExceptional`;
- `RHTower.boundedExponentEulerSource_pos_of_one_lt`;
- `RHTower.completeResolutionCarrierPrefix_pos_of_one_lt`;
- `RHTower.mobiusExceptionalBoundary_neg_of_one_lt`;
- `RHTower.eventually_completeResolutionCarrierPrefix_critical_re_neg`;
- `RHTower.eventually_completeResolution_critical_outside_dirichletHalfPlane`;
- `RHTower.meromorphicOrderAt_mobiusExceptionalBoundary`.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/XiSourceNormalConeDivisorConservation.lean`
  exits successfully;
- explicit `.olean` compilation exits successfully;
- the main theorem and every new support theorem depend only on
  `propext`, `Classical.choice`, and `Quot.sound`;
- no numerical computation is used.
