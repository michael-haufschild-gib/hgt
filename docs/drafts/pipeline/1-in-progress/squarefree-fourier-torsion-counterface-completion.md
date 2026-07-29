# Squarefree Fourier--torsion counterface and the critical Sobolev fracture

- **ID:** `squarefree-fourier-torsion-counterface-completion`
- **Stage:** 1-in-progress
- **Type:** SOURCE-SPECIFIC COMPLETION THEOREM / THIRD-COMPLETION BASE
- **Scientific status:** `[PAPER-PROVED CORE] [NOT RH] [NOVELTY PROVISIONAL]`
  `[SIGNIFICANCE CONDITIONAL ON STRICT MELLIN GRAPH]`
- **Parents:**
  - `../2-fully-proven/squarefree-euler-modular-corona-curvature-colligation.md`
  - `../2-fully-proven/not_new_scientific_knowledge/dyadic-squarefree-euler-fock-source-factorization.md`
  - `prime-aperture-stokes-action-law.md`
  - `deninger-enhanced-adiabatic-milnor-calderon-vanishing-cycle.md`
  - Poisson summation and Möbius inversion
- **Statement:** The ordinary squarefree integer source has a canonical independent
  Fourier counterface before any divisor is read.  On the circle, its centered
  Fourier distribution is an absolutely convergent Möbius sum of positive
  torsion probability measures in every homogeneous negative Sobolev space
  \(\dot H^{-r}\), \(r>1/2\).  Prime covering maps are exact strict
  contractions.  The norm has a sharp nonzero residue at \(r=1/2\), while the
  vector itself leaves the critical Hilbert space.  On the line, the same
  theorem is the distributional Fourier identity between the positive
  squarefree Dirac comb and a compensated dense rational-comb counterface.
  Gaussian Mellin transport of the positive face is exactly
  \(\pi^{-s/2}\Gamma(s/2)Z_{\rm sq}(s)\).

## 1. Positive integer face

Use Fourier transform
\[
 \widehat f(\xi)=\int_{\mathbb R}f(x)e^{-2\pi i x\xi}\,dx.
\]
Put
\[
 \omega_{\rm sf}
 =\sum_{n\in\mathbb Z\setminus\{0\}}\mu^2(|n|)\delta_n.
 \tag{1}
\]
This is a positive tempered measure constructed from ordinary integers and
their prime factorization.  Since
\[
 \mu^2(n)=\sum_{d^2\mid n}\mu(d),
 \tag{2}
\]
one has in \(\mathcal S'(\mathbb R)\)
\[
 \omega_{\rm sf}
 =\sum_{d\geq1}\mu(d)
   \left(\omega_{d^2\mathbb Z}-\delta_0\right).
 \tag{3}
\]
The series is unconditionally convergent as a tempered distribution.  Indeed,
for \(f\in\mathcal S(\mathbb R)\) and every \(N>1\),
\[
 \left|
 \sum_{m\neq0}f(d^2m)
 \right|
 \leq C_{f,N}d^{-2N}\sum_{m\neq0}|m|^{-N},
 \tag{4}
\]
so even the series of absolute values over \(d\) converges.

## 2. Independent Fourier counterface

Poisson summation gives
\[
 \widehat{\omega_{a\mathbb Z}}
 =a^{-1}\omega_{a^{-1}\mathbb Z},
 \qquad
 \widehat{\delta_0}=dx.
 \tag{5}
\]
Applying the continuous Fourier automorphism of \(\mathcal S'\) term by term
to `(3)` yields
\[
 \boxed{
 \widehat{\omega_{\rm sf}}
 =\sum_{d\geq1}\mu(d)
 \left(
   d^{-2}\omega_{d^{-2}\mathbb Z}-dx
 \right).
 }
 \tag{6}
\]
The brackets in `(6)`, rather than their two terms separately, are the
canonical source packets.  Their action on a Schwartz test is
\[
 \left\langle
 d^{-2}\omega_{d^{-2}\mathbb Z}-dx,f
 \right\rangle
 =\sum_{m\neq0}\widehat f(d^2m),
 \tag{7}
\]
so `(6)` is again absolutely summable in every Schwartz-distribution
seminorm after choosing a sufficiently high decay order.

This is the required independent counterlattice at the paper level:

```text
positive source face:       squarefree points in the integer lattice;
counterface:                compensated rational torsion combs;
comparison morphism:        the ordinary Fourier transform;
all-prime strictness:       take the convergent bracket before separating
                            rational comb and Lebesgue compensation.
```

No zero, Xi divisor, spectral splitting, or fitted metric occurs in
`(1)`--`(7)`.

## 3. Circle torsion resolution

Let \(\nu_q\) be normalized Haar probability on the \(q\)-torsion subgroup
of \(\mathbb T=\mathbb R/\mathbb Z\).  Its Fourier coefficients are
\[
 \widehat{\nu_q}(n)=\mathbf 1_{q\mid n}.
 \tag{8}
\]
On mean-zero distributions define
\[
 \|T\|_{\dot H^{-r}}^2
 =\sum_{n\neq0}|\widehat T(n)|^2|n|^{-2r}.
 \tag{9}
\]
For \(r>1/2\),
\[
 \|\nu_{d^2}-1\|_{\dot H^{-r}}^2
 =2\zeta(2r)d^{-4r}.
 \tag{10}
\]
Therefore
\[
 W_{\rm sf}
 :=\sum_{d\geq1}\mu(d)(\nu_{d^2}-1)
 \tag{11}
\]
converges absolutely in \(\dot H^{-r}(\mathbb T)\) for every \(r>1/2\).
Equations `(2)` and `(8)` give
\[
 \widehat W_{\rm sf}(n)=\mu^2(|n|),\qquad n\neq0.
 \tag{12}
\]
Thus
\[
 \boxed{
 \|W_{\rm sf}\|_{\dot H^{-r}}^2
 =2\sum_{n\geq1}{\mu^2(n)\over n^{2r}}
 =2Z_{\rm sq}(2r).
 }
 \tag{13}
\]

The completion wall and its residue are sharp:
\[
 W_{\rm sf}\in\dot H^{-r}
 \Longleftrightarrow r>{1\over2},
 \qquad
 \lim_{r\downarrow1/2}
 (2r-1)\|W_{\rm sf}\|_{\dot H^{-r}}^2
 ={2\over\zeta(2)}.
 \tag{14}
\]
The first assertion follows from the pole of
\(Z_{\rm sq}(u)=\zeta(u)/\zeta(2u)\) at \(u=1\); the second is its residue.
Hence the source has a finite nonzero critical metric residue but no vector
in the endpoint Hilbert space.

## 4. Exact prime contraction

For a prime \(p\), let
\[
 C_pT(x)=T(px)
 \tag{15}
\]
on Fourier series.  If \(a_n=\widehat T(n)\), then
\[
 \widehat{C_pT}(m)
 =
 \begin{cases}
 a_{m/p},&p\mid m,\\
 0,&p\nmid m.
 \end{cases}
 \tag{16}
\]
Consequently
\[
 \boxed{
 \|C_pT\|_{\dot H^{-r}}=p^{-r}\|T\|_{\dot H^{-r}}.
 }
 \tag{17}
\]
Thus the ordinary-prime covering semigroup is contractive on every member
of the Hausdorff Hilbert scale, and \(p^rC_p\) is isometric.  The failure of
\(W_{\rm sf}\) to be an eigenvector is the arithmetic Wold range defect:
at Fourier mode \(pn\), `(16)` reads \(\mu^2(n)\), whereas `(12)` reads
\(\mu^2(pn)\).  The discrepancy is exactly the \(p^2\)-divisibility
incidence, not an arbitrary compact error.

## 5. Gamma/Mellin reporter is already attached

For \(t>0\), let \(g_t(x)=e^{-\pi t x^2}\).  Then
\[
 \Theta_{\rm sf}(t)
 :=\langle\omega_{\rm sf},g_t\rangle
 =2\sum_{n\geq1}\mu^2(n)e^{-\pi n^2t}.
 \tag{18}
\]
For \(\Re s>1\), Tonelli and the Gamma integral give
\[
 \boxed{
 \int_0^\infty
 \Theta_{\rm sf}(t)t^{s/2-1}\,dt
 =
 2\pi^{-s/2}\Gamma(s/2)Z_{\rm sq}(s).
 }
 \tag{19}
\]
Fourier transport of the Gaussian through `(6)` gives the independent
counterface of the same Mellin section.  Thus the Gamma reporter is not
adjoined after observing the divisor: it is the Mellin shadow of the
source-defined Fourier double `(1)`, `(6)`.

Since \(Z_{\rm sq}(s)=\zeta(s)/\zeta(2s)\), its strict-right zero divisor
is exactly the strict-right zeta divisor.  Equation `(19)` therefore
attaches the correct distinguished section to the explicit source and
counterlattice before zeros are expanded.

## 6. What this closes

The construction supplies four items that were previously only demanded
axiomatically:

1. an integral source lattice;
2. a genuinely independent counterlattice;
3. a Hausdorff Hilbert scale on which every prime covering is a strict
   contraction; and
4. an exact Gamma/Mellin reporter whose distinguished section has the
   correct divisor.

It also explains why the all-prime object must precede scalar
specialization.  Separating the two terms in each bracket of `(6)` creates
the divergent Mertens coefficient \(M(D)\,dx\); retaining the compensated
packet makes the Fourier limit rapidly convergent on Schwartz tests.

## 7. Hostile audit: why this is not RH

1. **Endpoint escape.**  The source does not belong to
   \(\dot H^{-1/2}\).  Replacing `(14)` by its residue seminorm yields a
   Besicovitch-type completion that averages away density-zero data, hence
   cannot retain every isolated Xi conormal.
2. **Regularized evaluation.**  Point evaluation of `(11)` at the common
   torsion point is not continuous in \(\dot H^{-r}\).  Equation `(19)`
   gives the meromorphic section, but it does not make division by that
   section bounded or closable at a zero.
3. **Too-large safe scale.**  Every \(r>1/2\) is deliberately large enough
   to retain many polynomially twisted distributions.  Contractivity of
   `(17)` on that scale does not force a divisor character to be unitary.
4. **No exceptional positivity theorem.**  Fourier unitarity gives
   positivity on ordinary Schwartz squares.  Analytic continuation of the
   Mellin reporter leaves that cone; continuing its positivity would be
   the missing Hardy--Green theorem, not a consequence of `(6)`.
5. **No generalized-prime shortcut.**  A Beurling Euler system has no
   canonical embedding into the ordinary integer torsion tower `(8)`.
   This rejects the existing positive off-line generalized-prime
   countermodels as instances of this construction, but rejection alone
   supplies no inequality for zeta.

## 8. Positive survivor and next non-parent theorem

The third completion cannot be the endpoint Sobolev residue alone.  It
must be a strict relative refinement of the Fourier double:

```text
critical Sobolev residue
  + compensated torsion-comb Fourier counterface
  + source-defined Mellin/Gamma graph
  + Stokes aperture germ
  + point-conormal strict topology.
```

The first genuinely RH-bearing theorem is now concrete:

> **[FROZEN CONJECTURE -- STRICT FOURIER--MELLIN COUNTERFACE
> CONSERVATION.]**  The relative graph of `(6)` and `(19)`, completed over
> the full critical Sobolev/aperture scale before evaluation, has a
> source-defined positive exceptional quotient.  Fourier transport and
> prime coverings act nonexpansively on every finite matrix level, while
> every principal and higher Xi conormal survives in the strict graph
> topology.  Under the existing squarefree-to-Hardy localization, its
> exceptional second fundamental form is \(P_{\rm anti}Q_{\rm sq}=\ell_E\).

The conjecture is not counted as proved progress.  Clauses about conormal
survival and exceptional nonexpansivity remain the open core.  Its gain
over the previous specification is that source lattice, counterlattice,
comparison morphism, contraction scale, critical escape, and distinguished
Mellin section are now explicit formulas rather than placeholders.

## 9. Literature boundary

Parent mathematics includes Möbius inclusion--exclusion, Poisson
summation for lattice combs, Mellin transforms of theta series,
distributional Fourier transforms, negative Sobolev spaces, and
diffraction of \(k\)-free integers.  In particular:

- Baake--Moody--Pleasants determine autocorrelation and diffraction for
  \(k\)-free integers;
- Unterberger develops Dirichlet-series spectral decompositions of
  automorphic combs and Poisson-type summation formulas.

The autocorrelation/diffraction measure is not `(6)`: squaring Fourier
amplitudes loses the signed compensated counterface and the Mellin divisor
section.  Targeted searches have not located the joint theorem
`(6)`--`(19)` interpreted as a prime-contracting critical
source/counterlattice for the squarefree Gamma reporter.  This is search
noncollision, not a priority certificate.  Specialist review is required
before promotion.

## Gates

- [x] audit internal squarefree, Wold, Gamma, aperture, and conormal routes
- [x] construct positive squarefree integer comb before divisor expansion
- [x] construct independent compensated Fourier counterface
- [x] prove absolute distributional convergence
- [x] construct circle torsion resolution
- [x] prove exact \(\dot H^{-r}\) norm and critical residue
- [x] prove exact prime-cover contraction
- [x] attach the Gamma/Mellin squarefree reporter
- [x] reject endpoint residue as a conormal-faithful completion
- [x] reject generalized-prime systems lacking ordinary integer torsion
- [ ] specialist novelty audit
- [ ] construct strict critical Fourier--Mellin graph
- [ ] prove conormal and multiplicity-jet survival without divisor-fitted
      topology
- [ ] prove complete-matrix exceptional nonexpansivity
- [ ] identify exceptional second fundamental form with \(\ell_E\)
- [ ] RH

## Log

- 2026-07-29 — Constructed the explicit squarefree Fourier counterface.
  Proved its torsion resolution, negative-Sobolev convergence, sharp
  critical residue, prime contraction law, and Gamma/Mellin attachment.
  Hostile audit rejected the critical residue completion because it loses
  isolated conormals.  Froze the strict relative Fourier--Mellin graph as
  the next source-specific theorem.
