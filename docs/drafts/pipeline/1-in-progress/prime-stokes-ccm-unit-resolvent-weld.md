# Prime-Stokes/CCM unit-resolvent weld

- **ID:** `prime-stokes-ccm-unit-resolvent-weld`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / THIRD-COMPLETION PRODUCER
- **Scientific status:** `[PAPER-PROVED] [SOURCE-PURE] [NOT RH]`
  `[PARENT FOURIER/REPRODUCING-KERNEL ANALYSIS]`
  `[CORPUS-NEW EULER-STOKES/CCM WELD]`
  `[EXTERNAL NOVELTY UNVERIFIED]`
- **Parents:**
  - `prime-aperture-stokes-action-law.md`
  - `../2-fully-proven/new_scientific_knowledge/ccm-critical-mellin-aperture-resolvent-law.md`
  - `../4-publication-ready/arithmetic-julia-normal-cone/main.tex`
  - `../2-fully-proven/not_new_scientific_knowledge/euler-region-pointwise-schur-gap-nonlocal-index-law.md`
- **Statement:** The nested prime-aperture boundary layer has an explicit positive residue Pick
  kernel.  Every fixed aperture action has Fourier blind frequencies, but continuous aperture
  averaging removes them.  The unit exponential law gives a uniformly coercive residue metric
  with exact bounds \(2\) and \(4\).  The same law is uniquely selected by the independent CCM
  Volterra--Haar source because, and only because, both aperture transforms become the same
  right-half-plane resolvent \(1/(1+w)\), with opposite source/reporter orientation.

## 1. The nested Stokes microscope

Fix \(c>0\), put

\[
 \sigma=1+\varepsilon,\qquad
 X_c(\varepsilon)=\exp(c/\varepsilon^2),
\]

and use the boundary-layer reporter

\[
 s=\sigma+\varepsilon^2\eta,\qquad \Re\eta>0.             \tag{1}
\]

Let the omitted annular Euler transport be

\[
 u_{c,\varepsilon}(\eta)
 =
 U_{X_c,\infty}(1+\varepsilon,
                 1+\varepsilon+\varepsilon^2\eta)
 =
 \prod_{p>X_c}
 {1-p^{-1-\varepsilon}
  \over1+p^{-1-\varepsilon-\varepsilon^2\eta}}.          \tag{2}
\]

The local-factor estimate

\[
 |1+p^{-s}|\geq1-p^{-\Re s}\geq1-p^{-\sigma}
\]

shows that \(u_{c,\varepsilon}\) is Schur on the half-plane
\(\Re\eta>0\).

Put

\[
 a_c(\varepsilon)
 ={\varepsilon\over c}e^{-c/\varepsilon}.                \tag{3}
\]

The coupled critical-Mellin asymptotic from the parent card, with
\(z=1+\varepsilon\eta\), gives locally uniformly on
\(\Re\eta>0\)

\[
 {1-u_{c,\varepsilon}(\eta)\over a_c(\varepsilon)}
 \longrightarrow 1+e^{-c\eta}.                          \tag{4}
\]

Indeed the logarithm of \(u^{-1}\) is

\[
 E_1(c/\varepsilon)
 +E_1(c/\varepsilon+c\eta)
 +o(a_c(\varepsilon)),
\]

and the two exponential-integral terms divided by `(3)` tend to
\(1\) and \(e^{-c\eta}\), respectively.  Since the logarithm tends
to zero, replacing it by \(1-u\) changes only
\(o(a_c(\varepsilon))\).

## 2. Residue Pick kernel

For \(\Re\eta,\Re\theta>0\), define

\[
 K_{c,\varepsilon}(\eta,\theta)
 =
 {1-u_{c,\varepsilon}(\eta)
       \overline{u_{c,\varepsilon}(\theta)}
  \over\eta+\overline\theta}.                            \tag{5}
\]

Every finite matrix of `(5)` is positive semidefinite by Schur
contractivity.  Equation `(4)` yields

\[
 {K_{c,\varepsilon}(\eta,\theta)\over a_c(\varepsilon)}
 \longrightarrow
 K_c(\eta,\theta)
 :={2+e^{-c\eta}+e^{-c\overline\theta}
    \over\eta+\overline\theta}.                          \tag{6}
\]

Thus \(K_c\) is a positive kernel.  This is the literal residue
Hilbert metric missing from a scalar WKB valuation.

Let \(H=L^2(0,\infty)\), let

\[
 k_\eta(t)=e^{-\eta t},\qquad
 (L_cf)(t)=f(t+c),
\]

and put

\[
 G_c=2I+L_c+L_c^*.                                      \tag{7}
\]

Then

\[
 K_c(\eta,\theta)
 =\langle G_ck_\eta,k_\theta\rangle_H.                  \tag{8}
\]

For \(f\in H\), extend \(f\) by zero to the real line.  Plancherel
gives

\[
 \langle G_cf,f\rangle
 ={1\over2\pi}\int_{\mathbb R}
   \left(2+2\cos(c\xi)\right)|\widehat f(\xi)|^2\,d\xi.
                                                               \tag{9}
\]

Hence \(G_c\geq0\), but \(G_c\) is not coercive.  Wave packets
concentrated near

\[
 \xi=(2m+1)\pi/c
\]

are approximate null vectors.  One aperture action retains a
positive residue fibre but still has blind frequencies.

## 3. Continuous aperture action restores coercivity

Let \(\mu\) be a probability measure on \((0,\infty)\), and define

\[
\begin{aligned}
 K_\mu(\eta,\theta)&=\int K_c(\eta,\theta)\,d\mu(c),\\
 A_\mu&=\int L_c\,d\mu(c),\\
 G_\mu&=2I+A_\mu+A_\mu^*.
                                                               \tag{10}
\end{aligned}
\]

Then

\[
 K_\mu(\eta,\theta)
 =\langle G_\mu k_\eta,k_\theta\rangle                  \tag{11}
\]

and

\[
 \langle G_\mu f,f\rangle
 ={1\over2\pi}\int_{\mathbb R}
 \left[
   2+2\int_0^\infty\cos(c\xi)\,d\mu(c)
 \right]|\widehat f(\xi)|^2\,d\xi.                      \tag{12}
\]

If \(\mu\) has an \(L^1\) density which is positive on a
nondegenerate interval, the multiplier in square brackets has a
strict positive lower bound.  It cannot vanish at a finite
\(\xi\), because equality would require
\(\cos(c\xi)=-1\) for \(\mu\)-almost every \(c\).  It tends to \(2\)
as \(|\xi|\to\infty\) by the Riemann--Lebesgue lemma.  Continuity and
compactness on the remaining bounded interval give the positive
minimum.

Thus a continuous family of aperture actions is not decorative:
it converts the non-Hausdorff fixed-\(c\) residue metric into an
equivalent Hilbert norm.

## 4. Unit exponential law and exact coercivity

For \(a>0\), take

\[
 d\mu_a(c)=a e^{-ac}\,dc.                               \tag{13}
\]

Its Laplace transform is

\[
 \phi_a(\eta)
 =\int_0^\infty e^{-c\eta}\,d\mu_a(c)
 ={a\over a+\eta}.                                      \tag{14}
\]

Therefore

\[
 K_{\mu_a}(\eta,\theta)
 =
 {2+{a\over a+\eta}
      +{a\over a+\overline\theta}
  \over\eta+\overline\theta}.                           \tag{15}
\]

At the unit rate \(a=1\), `(12)` has the exact Fourier multiplier

\[
 m_1(\xi)
 =2+2\int_0^\infty e^{-c}\cos(c\xi)\,dc
 =2+{2\over1+\xi^2}.                                    \tag{16}
\]

Consequently

\[
 2I\leq G_{\mu_1}\leq4I.                                \tag{17}
\]

This gives a canonical Hausdorff, uniformly coercive local model for
the Stokes residue completion.  Its norm is equivalent to ordinary
Hardy \(L^2\), while its kernel still remembers the prime-aperture
source through `(4)`--`(6)`.

## 5. Unique weld to the independent CCM source

The parent CCM theorem gives, for \(\Re w>0\),

\[
 M_L(w)
 =-{(2w+1)(1-e^{-Lw})^2\over2w^2}                       \tag{18}
\]

and

\[
 \int_0^\infty e^{-aL}M_L(w)\,dL
 =-{2w+1\over a(a+w)(a+2w)}.                            \tag{19}
\]

Using the normalized exponential law `(13)`, the CCM average is

\[
 \mathcal C_a(w)
 =-{2w+1\over(a+w)(a+2w)}.                              \tag{20}
\]

The Euler-Stokes reporter residue average is \(\phi_a(w)=a/(a+w)\).
The identity

\[
 \mathcal C_a(w)=-\phi_a(w)
 \quad\hbox{for every }\Re w>0                           \tag{21}
\]

holds if and only if

\[
 {2w+1\over a+2w}=a
\quad\hbox{for every }w.
\]

Comparison of the \(w\)-coefficient and constant term gives

\[
 a=1.                                                    \tag{22}
\]

At that unique rate,

\[
 \phi_1(w)={1\over1+w},
\qquad
 \mathcal C_1(w)=-{1\over1+w}.                           \tag{23}
\]

Thus unit exponential averaging is not chosen to improve an
estimate.  It is uniquely selected by an exact compatibility between
two independently constructed source geometries:

```text
prime-aperture Stokes reporter residue
  = + unit right-half-plane resolvent;

CCM Volterra--Haar completed-error detector
  = - unit right-half-plane resolvent.                   (24)
```

The sign is the source/reporter orientation.  Equations `(17)` and
`(23)` give simultaneously a coercive residue metric and the exact
CCM causal resolvent.

## 6. What this advances and what remains open

This theorem constructs three pieces previously left hypothetical:

1. an explicit residue Pick kernel at every aperture action;
2. a continuum-aperture completion with a uniformly coercive
   Hilbert metric;
3. a unique source-selected aperture law which matches the CCM
   critical-Mellin detector.

It does **not** identify the Stokes boundary-layer coordinate
\(\eta\) with the centered Xi mode \(w=\rho-\tfrac12\).  Equality of
the rational formula \(1/(1+\cdot)\) does not construct that
intertwiner.

`[HOSTILE CORRECTION]` The bounded version of the former
`UNIT-RESOLVENT GAMMA/CALDERON INTERTWINER` is false as a proposed
third completion.  By `(17)`, the unit metric is bounded above and
below by constants times the ambient \(L^2\) metric.  It therefore has
the same completion, continuous spectrum, and discontinuous boundary
point evaluations.  A bounded congruence built only from this metric
cannot recover Xi conormal fibres lost in scalar \(L^2\).  An
unbounded map would need a source-fixed domain; asserting continuity
of every Xi fibre on that domain is the RH-bearing theorem.

The positive replacement is proved in
`unit-exponential-wold-calderon-suspension.md`: partitioning the unit
exponential aperture measure into intervals of length \(\log q\)
gives exactly the source Wold/Haar weights
\((1-q^{-1})q^{-k}\), and the first-cell symbol is
\((1-q^{-(1+w)})/(1+w)\).  Thus the unit direct integral is useful as
a relative Wold--Calderón first-cell transgression, not as a new
Hilbert completion.

The remaining conjecture is correspondingly narrower:

> **[CONJECTURE -- SOURCE-EFFECTIVE WOLD--CALDERON PRODUCT
> CONSERVATIVITY.]**  Lift the coherent first-cell cocycle through the
> actual Euler--Gamma/BV relative Wold extension, form its
> six-channel finite-prime Ind-product before divisor
> specialization, and prove that its moderate boundary is the
> source-defined co-Poisson/Xi principal conormal map and is nonzero
> on every top multiplicity jet.

If this source comparison is conservative, its unitary boundary
support forces every centered Xi dilation character to have modulus
one and hence proves RH.  The hard content is the source-derived
all-prime continuation and conservativity, not the scalar resolvent.

## 7. Hostile audit

1. Translation averaging, Plancherel, and coercivity of a nonlattice
   shift average are parent functional analysis.
2. Exponential aperture averaging and the CCM resolvent `(19)` are
   already proved in the corpus.
3. The new theorem is the arithmetic weld `(4)`--`(6)`,
   `(17)`, and the uniqueness statement `(21)`--`(23)`.
4. A fixed \(c\) is insufficient by the explicit blind-frequency
   theorem `(9)`.
5. An arbitrary positive aperture law is insufficient.  Unit rate
   is forced only after the independent CCM source is required.
6. The continuum real-aperture differential matroid is known to be
   blind to inserted rational quartets.  The residue metric alone
   therefore cannot select the Riemann divisor.  The conjectured
   intertwiner must use the actual-prime Julia-to-Xi transgression,
   which fails under target-only quartet surgery.
7. Equality of two scalar resolvents is not the missing intertwiner.
   Claiming RH from `(23)` would be theatre.
8. The exact bounds `(17)` prove a stronger no-go: the unit averaged
   form is norm-equivalent to ambient \(L^2\), so it cannot change
   which point fibres are continuous.
9. No bounded Hardy closure can recover the full prime logarithmic
   clock.  The surviving comparison is the relative first-cell
   cocycle, not a bounded repair of that closed graph.

## 8. Novelty boundary

The following are parent:

- de Branges--Rovnyak/Pick kernels of Schur multipliers;
- Fourier multipliers of translation averages;
- Riemann--Lebesgue coercivity for nonlattice averages;
- exponential-integral endpoint asymptotics;
- the corpus's CCM aperture-resolvent formula.

Targeted corpus search found no previous occurrence of the
prime-aperture residue kernel `(6)`, its fixed-action blind-frequency
classification `(9)`, the exact unit bounds `(17)`, or the unique
Euler-Stokes/CCM resolvent weld `(21)`--`(23)`.

External novelty remains unverified.  No priority claim is made.

## Gates

- [x] nested Stokes reporter asymptotic
- [x] residue Pick kernel constructed
- [x] fixed-action positivity and noncoercivity classified
- [x] continuum-aperture coercivity proved
- [x] unit exponential metric computed with exact bounds \(2,4\)
- [x] unique unit-rate Euler-Stokes/CCM resolvent weld proved
- [x] rational-quartet and scalar-resolvent hostile audits
- [x] dependency-closed blindness/coercivity/weld core formalized
- [x] bounded Gamma/Calderon completion route retired
- [x] unit Wold--Calderon first-cell survivor extracted
- [ ] external specialist novelty/significance audit
- [ ] construct source-effective all-prime Wold--Calderon product
- [ ] prove its Xi conormal conservativity
- [ ] RH

## Log

- 2026-07-28 — Derived the nested Stokes residue kernel, proved that
  fixed aperture action has Fourier blind frequencies, and proved
  continuous action averaging is coercive.  Unit exponential
  averaging gives exact metric bounds \(2\) and \(4\).  Its Laplace
  resolvent uniquely matches the independent CCM aperture-resolvent
  detector, isolating one explicit Gamma/Calderon intertwiner as the
  remaining RH-bearing theorem.
- 2026-07-28 — Formalized the dependency-closed core in
  `PrimeStokesCCMUnitResolventWeld.lean`.  The exact \(2,4\) bounds
  show the averaged metric is topologically equivalent to ambient
  \(L^2\), so the bounded-intertwiner route cannot restore divisor
  fibres.  Replaced it by the exact Wold--Calderón first-cell
  transgression and the source-effective all-prime product
  conservativity conjecture.
