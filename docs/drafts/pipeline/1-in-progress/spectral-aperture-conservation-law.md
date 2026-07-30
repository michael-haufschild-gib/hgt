# Spectral aperture conservation law

- **Status:** candidate universal parent law under proof and novelty audit
- **Target:** general-journal paper with an RH-facing arithmetic application
- **Replaces as headline:** Cayley/Fock order-space packet identity

## Question answered

What is the missing object seen only partially by Julia orientation, the \(8\pi\) Ward index,
Cayley/Fock order escape, Hedenmalm positivity, prime-source continuation, Weil energy, and
hypertranscendental divisor frames?

## Candidate answer

The object is the **spectral aperture**

\[
  \mathcal A_\Xi
  =\sup_{\xi(\rho)=0}\left|\Re\rho-\frac12\right|.
\]

It is a support function, not a scalar mass or a finite jet.  Orientation is retained by the
two-sided support function before any squaring or scalarization.

The parent theorem is index-free.  For every admissible conjugation-stable discrete spectral
family \(A=\{\alpha_j\}\) with finite height shells and summable heat trace,

\[
  \forall j,\ |\Im\alpha_j|\le \lambda
  \quad\Longleftrightarrow\quad
  \exists \sigma,C>0:\ 
  \left|\sum_j e^{-(\sigma+iu)\alpha_j}\right|
  \le C e^{\lambda|u|}\quad(u\in\mathbb R).
\]

Hence transverse support radius is exactly vertical exponential type.  This is a
support--indicator duality robust against cancellation: Phragmén--Lindelöf propagation, shell
extraction, and finite real-exponential rigidity recover every spectral point from one trace
growth envelope.

## Xi conservation law

For every nonnegative aperture \(\lambda\), the following are the same datum:

1. every Xi zero satisfies \(|\Re\rho-\tfrac12|\le\lambda\);
2. the canonical Poisson divisor trace has vertical type at most \(\lambda\);
3. every complete Hedenmalm Gaussian Hankel tower is positive beyond aperture \(\lambda\);
4. the inverse-tilted prime source and critical-Mellin defect are holomorphic beyond their
   translated \(\lambda\)-boundaries;
5. the explicit finite-prime--Gamma negative source has energy/Dirichlet abscissa bounded by
   \(\lambda\);
6. the projective reflection radius is at most \(\lambda\);
7. the supremal principal Hurwitz monodromy phase is at most \(\lambda\).

Their common admissible parameter set is the closed ray

\[
  [\mathcal A_\Xi,\infty).
\]

The RH is the zero-aperture endpoint \(\mathcal A_\Xi=0\).

## What the previous results become

- Julia squaring preserves divisor support but erases the signed support function.
- The \(8\pi\) Ward index measures total off-line mass, not support radius; no mass upper bound
  can substitute for aperture control.
- Cayley/Fock packets explain how a fixed defect escapes finite order while conserving its
  local coordinates.  The aperture law explains the global invariant those packets report.
- Compact windows and finite jets are finite projections; exponential type is an asymptotic
  support observable and therefore survives height/order escape.
- Relative differential-algebraic independence of the positive shell frame removes every
  finite differential explanation of the common divisor.  Aperture conservation identifies
  the genuinely global datum still shared by all shells.
- HGT contributes the unexpected arithmetic chart: open-strip principal Hurwitz monodromy phase
  is exactly horizontal Xi displacement, without phase aliasing.

## New route

The route is no longer “prove an unexplained positivity condition.”  It is:

\[
  \text{prove any source-side subexponential bound}
  \Longrightarrow \mathcal A_\Xi=0
  \Longrightarrow \mathrm{RH}.
\]

The fixed-width prime--Gamma/Weil source already has the exact sharp exponent
\(\mathcal A_\Xi\).  Thus every genuine improvement in its source growth is automatically a
quantitative zero-free region, and an \(n^{o(1)}\) bound is exactly the zero-aperture transition.

## Hostile gates

- [ ] Verify the abstract support--indicator law against classical indicator-diagram,
      Dirichlet-series, Laplace-transform, and non-self-adjoint heat-trace literature.
- [ ] Separate new theorem from classical Paley--Wiener support duality.
- [ ] Show the Xi arithmetic transport is not a tuple of tautological equivalences.
- [ ] Explain why the prime--Gamma coefficient is source-defined and finite at each sample.
- [ ] Integrate the positive hypertranscendental shell frame without implying that
      hypertranscendence itself constrains zero location.
- [ ] State precisely what the law answers and what it does not: it reconstructs the exact
      obstruction and opens a source-growth route; it does not currently prove
      \(\mathcal A_\Xi=0\).
- [ ] Reject Nature-level claims unless an external novelty review finds a genuinely broad
      conceptual consequence beyond RH reformulation.
