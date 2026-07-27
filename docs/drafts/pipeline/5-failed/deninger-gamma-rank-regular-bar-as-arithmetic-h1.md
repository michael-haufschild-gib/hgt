# Gamma-rank regular bar complex is not arithmetic \(H^1\)

- **ID:** `deninger-gamma-rank-regular-bar-as-arithmetic-h1`
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Parent:** `deninger-mw-gamma-brst-complex`
- **Statement:** the doubled regular representation of
  \(\mathbb Q_{>0}^{\times}\) is a valid positive auxiliary local
  system, but its canonical reduced \(\ell^2\) bar completion cannot be
  Deninger's nontrivial arithmetic middle cohomology.

## Killing mechanism

Let
\[
 G=\mathbb Q_{>0}^{\times},\qquad
 K=\ell^2(G,\mathbb C).
\]
The source module in
`DAC_DENINGER_GAMMA_RANK_REGULAR_REPRESENTATION` uses
\[
 U_a e_q=e_{aq}.                                               \tag{1}
\]

First, `(1)` is not the Frobenius pullback on Deninger's unitary
character phase.  Fourier transform identifies \(K\) with
\(L^2(\widehat G)\), where `(1)` is multiplication by
\(\chi\mapsto\chi(a)\).  Frobenius/power pullback
\(\chi\mapsto\chi^a\) instead sends \(e_q\) to \(e_{q^a}\).  The
regular module is therefore the deck-group regular local system, not
the unitary phase and not the Hilbert--Kummer radial flow.

Second,
\[
 G\cong\bigoplus_{p\ {\rm prime}}\mathbb Z
\]
is countable, infinite, and amenable.  Cheeger--Gromov vanishing
therefore gives
\[
 \overline H^n_{(2)}(G)=0\qquad(n\ge0)                         \tag{2}
\]
for the standard reduced \(\ell^2\) bar complex.  Doubling \(K\) and
adding the positive quaternionic operator does not change `(2)`.
Consequently the canonical cofinal reduced harmonic completion of the
bare Gamma-rank bar channel has no nonzero middle class.  Finite
cutoff harmonic vectors can only survive if a different arithmetic
incidence differential and topology are constructed and proved not to
converge to this standard regular bar completion.

Equation `(2)` does not say every algebraic or unreduced bar quotient
vanishes.  For infinite groups the unreduced image may be nonclosed.
Deninger's desired cohomology is reduced/Hausdorff, so nonclosed-range
classes are not an admissible substitute.

## No-go closure

- **Exact killed route:** define arithmetic \(H^1\) as reduced
  cohomology of the standard \(\ell^2(G)\)-regular power-bar complex.
- **Positive survivor:** the doubled regular representation remains a
  source-defined positive auxiliary deck local system.  Its centered
  shifts are unitary, its cup/Hodge algebra is valid, and it can test
  finite correspondence formulas.
- **Replacement source:** Deninger's coefficient is the degreewise
  invariant Tate--Milnor sheaf.  Its Hilbert--Kummer radius realizes
  the Poisson differential through actual flow pullbacks, and its
  canonical half-density circle gives the positive-radius complex
  Kähler leaves.
- **New insight:** the regular shift, phase Frobenius, and radial flow
  are three distinct representations.  Identifying them hides both a
  Fourier-type error and reduced-\(\ell^2\) acyclicity.

## References

- Jeff Cheeger and Mikhail Gromov, *L2-cohomology and group
  cohomology*, Topology 25 (1986), 189--215.
- Henrik Densing Petersen, *L2-Betti Numbers of Locally Compact
  Groups*, arXiv:1104.3294.

## Log

- 2026-07-27 — Retired the standard regular-bar completion as
  arithmetic \(H^1\); retained its positive finite/source local-system
  algebra.
