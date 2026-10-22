# Prime-aperture Stokes action at the Euler critical wall

- **ID:** `prime-aperture-stokes-action-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / THIRD-COMPLETION CORRECTION
- **Scientific status:** `[PAPER-PROVED] [SOURCE-PURE] [NOT RH]`
  `[ARITHMETIC ASYMPTOTICS ARE PARENT THEORY]`
  `[CORPUS-NEW APERTURE-STOKES INTERPRETATION]`
  `[EXTERNAL NOVELTY UNVERIFIED]`
- **Parents:**
  - `../2-fully-proven/mobius-pluecker-normal-cone-diagonal-lift.md`
  - `squarefree-euler-modular-corona-curvature-colligation.md`
  - `deninger-mertens-adiabatic-exponential-corner.md`
  - `deninger-enhanced-adiabatic-milnor-calderon-vanishing-cycle.md`
- **Statement:** The prime-aperture rate is a genuine exponential boundary coordinate.  If
  \(\sigma=1+\varepsilon\) and the finite aperture contains the primes
  \(p\leq X_c(\varepsilon)=\exp(c/\varepsilon^2)\), then both the omitted reciprocal
  Pluecker-transfer tail and the omitted critically rescaled squarefree Fisher-capacity tail are
  flat to every algebraic order but have exact WKB action \(c\).  Therefore an
  exponential/transseries third completion cannot be independent of arbitrary cofinal prime
  exhaustions.  It must retain \(c=\varepsilon^2\log X\) as an aperture/Stokes coordinate and ask
  for covariant transport across that face.

## 1. Why the cutoff rate is load-bearing

The existing cofinal diagonal theorem starts from

```text
M_(S,sigma)(s)
 =product_(p in S) (1-p^(-sigma))/(1+p^(-s))             (1)
```

and, for every sequence \(\varepsilon_n\downarrow0\), selects finite prime sets \(S_n\) such that

```text
M_(S_n,1+epsilon_n)(s)/epsilon_n -> 1/Z_sq(s)             (2)
```

locally uniformly on \(\Re s>1\).  Its compact-exhaustion proof gives existence but does not
control how fast \(S_n\) grows.  That omission is harmless in ordinary locally uniform topology.
It is not harmless in the enhanced completion proposed by the parent cards, because that
completion explicitly retains exponentially flat errors.

Fix \(c>0\), put

\[
 X_c(\varepsilon)=\exp(c/\varepsilon^2),\qquad
 S_{c,\varepsilon}=\{p:p\leq X_c(\varepsilon)\}.          \tag{3}
\]

The scale

\[
 c=\varepsilon^2\log X_c(\varepsilon)                    \tag{4}
\]

is the finite nonzero chart of the new boundary face.

## 2. Prime-tail asymptotics

Let

\[
 A_c(\varepsilon)
 =\sum_{p>X_c(\varepsilon)}p^{-1-\varepsilon}.           \tag{5}
\]

The prime number theorem and partial summation give, uniformly for every fixed \(c>0\),

\[
 A_c(\varepsilon)
 \sim
 \int_{X_c(\varepsilon)}^\infty
   {t^{-1-\varepsilon}\over\log t}\,dt.                  \tag{6}
\]

With \(u=\varepsilon\log t\), the integral in `(6)` is

\[
 E_1(c/\varepsilon)
 =\int_{c/\varepsilon}^\infty {e^{-u}\over u}\,du
 \sim{\varepsilon\over c}e^{-c/\varepsilon}.             \tag{7}
\]

Consequently

\[
 A_c(\varepsilon)
 \sim{\varepsilon\over c}e^{-c/\varepsilon},
 \qquad
 -\varepsilon\log A_c(\varepsilon)\longrightarrow c.    \tag{8}
\]

The use of the prime number theorem in `(6)` is unconditional.  If
\(\pi(t)=\operatorname{Li}(t)(1+r(t))\), then
\(\sup_{t\geq X}|r(t)|\to0\); partial summation against the positive decreasing weight
\(t^{-1-\varepsilon}\) transfers this uniform relative error to `(6)`.

## 3. Reciprocal Pluecker-transfer tail

Let

\[
 M_\sigma(s)
 ={1\over\zeta(\sigma)Z_{\rm sq}(s)}
 =\prod_p{1-p^{-\sigma}\over1+p^{-s}}.                  \tag{9}
\]

For a compact \(K\Subset\{\Re s>1\}\), put
\(\delta=\min_{s\in K}(\Re s-1)>0\).  From `(1)` and `(9)`,

\[
 {M_{S_{c,\varepsilon},1+\varepsilon}(s)
   \over M_{1+\varepsilon}(s)}
 =
 \prod_{p>X_c(\varepsilon)}
 {1+p^{-s}\over1-p^{-1-\varepsilon}}.                  \tag{10}
\]

The logarithm of `(10)` is

\[
 L_c(\varepsilon,s)
 =
 \sum_{p>X_c}
 \left[
   \log(1+p^{-s})-\log(1-p^{-1-\varepsilon})
 \right].                                               \tag{11}
\]

Uniformly on \(K\),

\[
 L_c(\varepsilon,s)
 =A_c(\varepsilon)(1+o(1)).                              \tag{12}
\]

Indeed, the \(k\geq2\) denominator terms are bounded by a constant times
\(\sum_{n>X_c}n^{-2-2\varepsilon}\), while the numerator is bounded by a constant times
\(\sum_{n>X_c}n^{-1-\delta}\).  Both are
\(\exp(-\Theta(\varepsilon^{-2}))\), hence negligible compared with `(7)`.

Since \(A_c(\varepsilon)\to0\), equations `(10)`--`(12)` give

\[
 {M_{S_{c,\varepsilon},1+\varepsilon}(s)
   \over M_{1+\varepsilon}(s)}
 -1
 \sim{\varepsilon\over c}e^{-c/\varepsilon}              \tag{13}
\]

locally uniformly on \(\Re s>1\).  The residue unit

\[
 G(1+\varepsilon)=\varepsilon\zeta(1+\varepsilon)\to1
\]

therefore yields

\[
 {M_{S_{c,\varepsilon},1+\varepsilon}(s)\over\varepsilon}
 \longrightarrow {1\over Z_{\rm sq}(s)},                \tag{14}
\]

and, more sharply,

\[
 {M_{S_{c,\varepsilon},1+\varepsilon}(s)
       -M_{1+\varepsilon}(s)\over\varepsilon}
 \sim
 {1\over Z_{\rm sq}(s)}
 {\varepsilon\over c}e^{-c/\varepsilon}.                \tag{15}
\]

Multiplication by the nonvanishing archimedean factor on the safe half-plane gives the same
statement for the Gamma-completed reciprocal section \(X_{\rm sq}^{-1}\).

## 4. Fisher-capacity tail on the same aperture

The squarefree Fisher variance is

\[
 V(\sigma)
 =\sum_p {(\log p)^2p^{-\sigma}\over(1+p^{-\sigma})^2}.  \tag{16}
\]

Let \(V_{\leq X}\) be its restriction to \(p\leq X\), and put

\[
 T_c(\varepsilon)
 =\varepsilon^2
  \left[V(1+\varepsilon)
        -V_{\leq X_c(\varepsilon)}(1+\varepsilon)\right]. \tag{17}
\]

The denominator in `(16)` tends uniformly to one on the omitted tail.  The prime number theorem
and partial summation therefore give

\[
\begin{aligned}
 T_c(\varepsilon)
 &\sim
 \varepsilon^2
 \int_{X_c(\varepsilon)}^\infty
  (\log t)t^{-1-\varepsilon}\,dt\\
 &=
 \left(1+{c\over\varepsilon}\right)e^{-c/\varepsilon}.
                                                               \tag{18}
\end{aligned}
\]

Hence

\[
 -\varepsilon\log T_c(\varepsilon)\longrightarrow c.    \tag{19}
\]

The full critically normalized source tangent has energy
\(4\varepsilon^2V(1+\varepsilon)\to4\).  Equation `(18)` proves that the hard-cut aperture `(3)`
preserves the four-unit limit and that its missing capacity is exponentially flat with the same
action \(c\) as the reciprocal-transfer error `(15)`.

## 5. Aperture-Stokes theorem

`[THEOREM] [DAC_PRIME_APERTURE_STOKES_ACTION]`

For every \(c>0\), the explicit finite-prime apertures `(3)` satisfy simultaneously:

1. the normalized finite reciprocal Pluecker transfer converges locally uniformly to
   \(Z_{\rm sq}^{-1}\), and after Gamma completion to \(X_{\rm sq}^{-1}\);
2. the finite squarefree Fisher tangent retains the full critical four-unit capacity;
3. the discarded analytic-transfer tail is flat to every algebraic order in \(\varepsilon\) and
   has WKB action \(c\);
4. the discarded critically rescaled Fisher-capacity tail is flat to every algebraic order and
   has the same WKB action \(c\).

The proof is `(5)`--`(19)`.

More generally, if \(X(\varepsilon)\to\infty\) and

\[
 \varepsilon^2\log X(\varepsilon)\longrightarrow c\in(0,\infty), \tag{20}
\]

the same action law holds.  If the left side of `(20)` tends to zero while
\(\varepsilon\log X\to\infty\), the ordinary transfer still converges but its
\(1/\varepsilon\)-WKB action is zero.  If it tends to infinity, the action is infinite.
Thus \(c\in[0,\infty]\) is an actual compactifying coordinate, not a chosen error tolerance.

## 6. Exact annular transport and boson--fermion curvature collapse

The source-selected transport exists before Gamma completion.  For
\(1<\sigma\), \(2\leq X<Y\leq\infty\), and initially
\(\Re s>1\), put

\[
 U_{X,Y}(\sigma,s)
 =\prod_{X<p\leq Y}{1-p^{-\sigma}\over1+p^{-s}}.          \tag{21}
\]

For \(X<Y<Z\),

\[
 U_{X,Z}=U_{X,Y}U_{Y,Z}.                                  \tag{22}
\]

Thus the finite apertures form an exact multiplicative transport
groupoid, not merely a collection of unrelated diagonals.  It is
contractive in its source Hardy polarization.  If \(\Re s\geq\sigma\),
then

\[
 |1+p^{-s}|\geq1-p^{-\Re s}\geq1-p^{-\sigma},
 \qquad |U_{X,Y}(\sigma,s)|\leq1.                         \tag{23}
\]

Hence every finite \(U_{X,Y}\) is a Schur multiplier on the half-plane
\(\Re s\geq\sigma\).  In particular its complete Pick kernel, not only
its pointwise modulus, is positive there.

The \(\sigma\)-curvature of this transport is

\[
\begin{aligned}
 B_{X,Y}(\sigma)
 &:=-\partial_\sigma^2\log U_{X,Y}(\sigma,s)\\
 &=\sum_{X<p\leq Y}
   {(\log p)^2p^{-\sigma}\over(1-p^{-\sigma})^2}.
                                                               \tag{24}
\end{aligned}
\]

It is independent of the spectral reporter \(s\).  Compare it with
the squarefree, or fermionic, Fisher curvature on the same annulus,

\[
 F_{X,Y}(\sigma)
 =\sum_{X<p\leq Y}
   {(\log p)^2p^{-\sigma}\over(1+p^{-\sigma})^2}.          \tag{25}
\]

Writing \(q=p^{-\sigma}\), the local identity

\[
 {q\over(1-q)^2}-{q\over(1+q)^2}
 ={4q^2\over(1-q^2)^2}                                   \tag{26}
\]

gives the exact positive decomposition

\[
 B_{X,Y}(\sigma)
 =F_{X,Y}(\sigma)
  +4\sum_{X<p\leq Y}
    {(\log p)^2p^{-2\sigma}\over(1-p^{-2\sigma})^2}.       \tag{27}
\]

The last term is precisely the even-prime-power correction.  For the
tail \(X=X_c(\varepsilon)\), \(\sigma=1+\varepsilon\),

\[
 \varepsilon^2B_{X_c,\infty}(1+\varepsilon)
 \sim
 \varepsilon^2F_{X_c,\infty}(1+\varepsilon)
 \sim
 \left(1+{c\over\varepsilon}\right)e^{-c/\varepsilon}.
                                                               \tag{28}
\]

Indeed `(18)` gives the second equivalence, while the correction in
`(27)` is bounded by

\[
 O\!\left(
   \varepsilon^{-2}
   \exp\!\left[-{c\over\varepsilon^2}
                -{2c\over\varepsilon}\right]\right),      \tag{29}
\]

which has infinite \(1/\varepsilon\)-WKB action.  Therefore the
bosonic transport curvature and positive squarefree Fisher curvature
are not only equal in action: their ratio tends to one at every
finite aperture action \(c\).  The exact discrepancy is carried by a
strictly deeper exponential grade.

This proves a source-side part of the previously conjectural
transport.  What remains open is its Gamma/Calderon continuation and
its action on the exceptional Hardy graph.

## 7. The first Stokes residue and why \(c\) alone is insufficient

The scalar limit \(c=\lim\varepsilon^2\log X\) records the exponential
action but not the associated-graded coefficient.  Let

\[
 \log X(\varepsilon)
 ={c\over\varepsilon^2}+{d\over\varepsilon}
   +o(\varepsilon^{-1}),\qquad c>0,\ d\in\mathbb R.        \tag{30}
\]

Then

\[
 \varepsilon\log X={c\over\varepsilon}+d+o(1),
                                                               \tag{31}
\]

and the same prime-number-theorem argument as above gives

\[
\begin{aligned}
 \sum_{p>X}p^{-1-\varepsilon}
 &\sim{\varepsilon\over c}e^{-c/\varepsilon}e^{-d},\\
 \varepsilon^2F_{X,\infty}(1+\varepsilon)
 &\sim{c\over\varepsilon}e^{-c/\varepsilon}e^{-d},\\
 \varepsilon^2B_{X,\infty}(1+\varepsilon)
 &\sim{c\over\varepsilon}e^{-c/\varepsilon}e^{-d}.
                                                               \tag{32}
\end{aligned}
\]

Consequently, locally uniformly for fixed \(\Re s>1\),

\[
\begin{aligned}
 {c\over\varepsilon}e^{c/\varepsilon}
 \left({M_{X,1+\varepsilon}(s)\over M_{1+\varepsilon}(s)}-1\right)
 &\longrightarrow e^{-d},\\
 {\varepsilon\over c}e^{c/\varepsilon}
 \varepsilon^2F_{X,\infty}(1+\varepsilon)
 &\longrightarrow e^{-d},\\
 {\varepsilon\over c}e^{c/\varepsilon}
 \varepsilon^2B_{X,\infty}(1+\varepsilon)
 &\longrightarrow e^{-d}.                               \tag{33}
\end{aligned}
\]

Thus the reciprocal-transfer defect and the two curvature readings
have the same first Stokes residue after their forced polynomial
normalizations.  This closes the leading-coefficient gap left open in
the first version of this card.

It also falsifies the earlier wording that all exhaustions with the
same \(c\) give equivalent enhanced fibres.  Changing \(d\) changes
the residue by \(e^{-d}\).  The correct structure is filtered:

```text
c = exponential valuation grade;
d and further aperture asymptotics = residue data inside gr^c;
annular Euler products U_(X,Y) = exact transition morphisms.
```

A Hahn--Rees or equivalent Stokes-filtered realization is therefore
natural, but merely naming a Hahn field is not a construction.  The
completion must retain the residue metric and the complete Schur
kernel of `(23)`.

## 8. Coupled critical-Mellin scaling: the source--reporter Stokes wall

The fixed-\(s\) limit in Sections 3 and 7 makes the leading Stokes
residue scalar because the spectral numerator tail is
superexponentially smaller.  That chart cannot carry a divisor
conormal.  The correct boundary chart scales the reporter together
with the source:

\[
 \sigma=1+\varepsilon,\qquad
 s=1+\varepsilon z,\qquad
 X=\exp(c/\varepsilon^2),\qquad \Re z>0.                 \tag{34}
\]

Let

\[
 \mathcal L_{c,\varepsilon}(z)
 =\log {M_{X,1+\varepsilon}(1+\varepsilon z)
             \over M_{1+\varepsilon}(1+\varepsilon z)}. \tag{35}
\]

Uniformly for \(z\) in compact subsets of \(\Re z>0\), prime-number
theorem partial summation and the large-argument expansion of \(E_1\)
give

\[
\begin{aligned}
 \mathcal L_{c,\varepsilon}(z)
 &=
 E_1(c/\varepsilon)+E_1(cz/\varepsilon)\\
 &\quad
 +o\!\left(\varepsilon
 e^{-c\min(1,\Re z)/\varepsilon}\right)\\
 &=
 {\varepsilon\over c}
 \left[
   e^{-c/\varepsilon}
   +{1\over z}e^{-cz/\varepsilon}
 \right]
 +o\!\left(\varepsilon
 e^{-c\min(1,\Re z)/\varepsilon}\right).             \tag{36}
\end{aligned}
\]

The higher local-factor powers remain
\(\exp[-\Theta(\varepsilon^{-2})]\).  Equation `(36)` has
two distinct exponential factors:

```text
source aperture packet:    exp(-c/epsilon);
spectral reporter packet:  exp(-c z/epsilon).            (37)
```

Their real actions are equal exactly when

\[
 \Re z=1
 \quad\Longleftrightarrow\quad
 \Re s=\sigma.                                           \tag{38}
\]

Thus the boundary of the exact Schur domain `(23)` is also the
source--reporter Stokes wall.  On \(z=1+i\tau\),

\[
 {c\over\varepsilon}e^{c/\varepsilon}
 \mathcal L_{c,\varepsilon}(1+i\tau)
 =
 1+{e^{-ic\tau/\varepsilon}\over1+i\tau}+o(1).           \tag{39}
\]

The oscillatory second factor is erased by the fixed-\(s\) chart but
survives in the enhanced boundary object.  This is the first
non-scalar exponential principal symbol produced directly by the
prime source.

`(21)`--`(39)` identify the structure the third completion must
transport:

```text
exact annular prime cocycle
  + complete Schur/Pick positivity on Re z >= 1
  + bosonic curvature = squarefree Fisher curvature in finite Stokes grade
  + two-factor enhanced symbol on the boundary wall.
```

Scalar WKB valuation alone is insufficient.  The corpus already shows
that one-node Schur positivity is unconditional while RH is an
all-correlation-order statement.  The load-bearing object is the
complete Stokes-graded Pick kernel of the annular cocycle.

## 9. Correction to the third-completion conjecture

The parent enhanced-adiabatic card currently asks for presentation independence under admissible
cofinal prime exhaustions.  That requirement is correct only after forgetting exponentially flat
terms.  It is false in the enhanced category which retains those terms: equations `(15)` and
`(18)` distinguish different finite values of \(c\).

The corrected base is at least the three-scale blow-up

```text
Euler criticality:       epsilon=sigma-1 ->0;
prime aperture:          X ->infinity;
Poisson/translation:     h ->0;

aperture Stokes chart:   c=epsilon^2 log X.              (40)
```

Required invariance is replaced by:

> **[CORRECTED CONJECTURE -- STOKES-FILTERED HAHN--REES/PICK COMPLETION.]**
> The enhanced all-prime Euler--Gamma/Calderon object extends the exact annular cocycle `(21)` to
> a Hausdorff Stokes-filtered pro-Hilbert object.  Its grade-\(c\) residue retains the full aperture
> germ, not only \(c\), and its transition maps preserve the complete Pick kernels induced by
> `(23)`.  On the coupled chart `(34)`, the two exponential packets in `(37)` extend to a
> source-defined exceptional graph.  Its bosonic residue metric is the squarefree Fisher residue
> metric from `(27)`--`(33)`, and its Gamma/Calderon vanishing cycle is the source-defined
> anti-Hardy conormal \(P_{\rm anti}Q_{\rm sq}=\ell_E\).  The continuation functor is
> nonexpansive on every finite Pick matrix.

The last two clauses are the RH-bearing theorem.  They are stronger than the paper theorem and
are not proved here.  If they hold, the existing complete negative-index formula forbids every
strict-right Xi zero; equivalently the four-unit one-vector shadow gives
\(\|\ell_E\|_2^2\leq4\).

## 10. Why this matters for hypertranscendental functions

The result exhibits an exact infinity phenomenon which finite differential jets cannot see:

```text
same ordinary cofinal limit
  + same finite-prime algebraic gauges
  + same four-unit limiting source capacity
  but different exponentially flat boundary actions c.          (41)
```

Thus a completion of an HT source can be presentation-independent at every algebraic/differential
grade and still retain a continuous family of inequivalent exponential boundary presentations.
The missing HT invariant is not another Taylor coefficient.  It is the Stokes transport of the
source graph across the cofinal-aperture face.

For RH, this removes one hidden ambiguity from the enhanced Gauss--Ward proposal.  A proof may not
select one diagonal by compact exhaustion and then call its exceptional metric canonical.  It
must either construct the \(c\)-transport and prove the relevant capacity independent under that
transport, or identify a source law selecting one \(c\)-section.

## 11. Hostile audit

1. The prime-number-theorem and exponential-integral asymptotics are parent mathematics.
2. The theorem does not continue a norm through \(\Re s=1/2\), bound \(\ell_E\), or prove RH.
3. Equations `(32)`--`(33)` identify the first residue coefficients after forced polynomial
   normalization; they do not construct the Gamma/Calderon continuation or an isometry.
4. Choosing \(c=1\) is not canonical.  The point is the whole \(c\)-face.
5. Ordinary locally uniform convergence erases `(15)` and cannot detect the obstruction.
6. A transseries completion that also erases `(15)` is not the completion forced by the
   first-trace exponential-flat graph fracture.
7. Generalized-prime countermodels remain a required test for any proposed Stokes transport.

8. The fixed-\(s\) leading residue is scalar.  Only the coupled chart `(34)` retains the spectral
   packet, and even that packet has not been transported to a Xi divisor fibre.
9. A Hahn-series vocabulary without a residue Hilbert metric and complete Pick-kernel functor is
   rejected as a redressing of the already-known rate-filtration RH criterion.

## 12. Literature boundary

Finite Euler-product error estimates near \(\Re s>1\), prime-number-theorem partial summation, and
the large-argument expansion of \(E_1\) are established.  Hybrid Euler--Hadamard products also use
the prime cutoff as a mediator between Euler and zero factors.

Targeted searches did not locate the joint statement that the reciprocal squarefree normal-cone
transfer tail and its critically rescaled Fisher-capacity tail have the same aperture action
\(\varepsilon^2\log X\), or the resulting obstruction to cofinal-exhaustion independence in an
enhanced HT completion.  This is search noncollision, not a priority certificate.

## Gates

- [x] isolate the cutoff rate omitted by the existence-only diagonal theorem
- [x] prove prime reciprocal-tail asymptotic
- [x] prove finite reciprocal-transfer convergence on the explicit aperture
- [x] compute exact transfer-tail WKB action
- [x] prove finite Fisher-capacity convergence on the same aperture
- [x] compute exact Fisher-tail WKB action
- [x] identify \(c=\varepsilon^2\log X\) as an additional boundary coordinate
- [x] construct the exact finite annular aperture cocycle
- [x] prove its Schur contractivity on the moving safe half-plane
- [x] identify its curvature with squarefree Fisher curvature modulo an infinite-action even tail
- [x] compute the common first Stokes residue and disprove same-\(c\) fibre equivalence
- [x] derive the two-factor coupled critical-Mellin symbol and its source--reporter Stokes wall
- [x] replace false cofinal independence by residue-sensitive aperture-Stokes covariance
- [ ] independent specialist novelty/significance audit
- [ ] formalize the dependency-closed tail theorem in Lean
- [x] construct source Stokes transport on the uncompleted Euler side
- [ ] extend the complete Stokes-graded Pick kernel through Gamma/Calderon continuation
- [ ] identify transported exceptional graph with the Hardy--Green conormal
- [ ] prove the four-unit estimate
- [ ] RH

## References

- S. M. Gonek, C. P. Hughes, and J. P. Keating,
  *A Hybrid Euler--Hadamard Product Formula for the Riemann Zeta Function*,
  arXiv:math/0511182.
- NIST Digital Library of Mathematical Functions, §8.20,
  asymptotic expansions of generalized exponential integrals.
- Prime number theorem and partial summation in their standard unconditional forms.

## Log

- 2026-07-28 — Proved the explicit prime-aperture Stokes action law.  The reciprocal exceptional
  section and four-unit Fisher tangent converge along the same apertures, while both omitted tails
  retain the cutoff action \(c=\varepsilon^2\log X\).  Corrected the third-completion target from
  arbitrary cofinal-exhaustion independence to covariance over an aperture/Stokes face.
- 2026-07-28 — Constructed the exact annular Euler transport, proved its Schur contractivity,
  and decomposed its bosonic curvature as squarefree Fisher curvature plus a deeper even tail.
  Computed the common first Stokes residue, correcting the false claim that the scalar action
  \(c\) determines an enhanced fibre.  On the coupled chart \(s=1+\varepsilon z\), derived the
  two-factor enhanced symbol and identified \(\Re z=1\) as the exact source--reporter Stokes wall.
