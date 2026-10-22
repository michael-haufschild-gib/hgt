# Source-horizon conservation of Riemann divisor information

- **ID:** `riemann-source-cayley-order-space-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL SOURCE-HORIZON THEOREM / NOVEL RH ROUTE
- **Supersedes as headline:** `riemann-complex-modular-character-law`
- **Status:** universal packet law already formalized; arithmetic residue realization and hostile novelty audit in progress

## Universal law

Every marked source \(c\) defines a neutral horizon
\[
  \operatorname{Re}\rho=\operatorname{Re}c-\frac12
\]
for divisor information.  This horizon is not imposed as a symmetry line: it is the zero-rate
locus of the exact source-residue semigroup.

For any meromorphic response, source \(c\), divisor point \(\rho\ne c\), residue \(m\), and
\(\tau\ge0\), put
\[
  x_{c,\rho}(\tau)=|\rho-c|^2\tau,\qquad
  \nu_c(\rho)=2\operatorname{Re}(\rho-c)+1.
\]
Then
\[
 \frac{x_{c,\rho}(\tau)^r}{r!}
 \left|\partial_x^r\!\left(m e^{x/(\rho-c)}\right)
   \bigg|_{x=x_{c,\rho}(\tau)}\right|^2
 =
 |m|^2e^{\nu_c(\rho)\tau}
 \Pr\{\operatorname{Pois}(\tau)=r\}.
\]
This is an exact identity, not an asymptotic statement.  All radial information has been converted
into observation time; the only surviving exponential datum is signed distance from the neutral
horizon.

Before taking norms, canonical observation gives the sharper inversion law
\[
  \frac{x_{c,\rho}(\tau)}{\rho-c}
    =\overline{\rho-c}\,\tau,\qquad
  m e^{x_{c,\rho}(\tau)/(\rho-c)}
    =m e^{\overline{\rho-c}\tau}.
\]
Reciprocal Cayley displacement becomes conjugate direct spectral displacement.  Radial escape is
therefore converted into oscillatory phase, not destroyed.  The raw mode energy contributes
\(e^{2\operatorname{Re}(\rho-c)\tau}\); summing the factorial derivative orders contributes the
Poisson entropy factor \(e^\tau\).  Their balance produces
\(\nu_c(\rho)=2\operatorname{Re}(\rho-c)+1\) and hence the neutral horizon.

The Riemann specialization is arithmetically forced: the completed prime response has source
\(c=1\), so its neutral horizon is exactly \(\operatorname{Re}\rho=1/2\).  For
\[
 \rho_T=\frac12+a+iT,\qquad
 x_T(\tau)=\tau\left((a-\tfrac12)^2+T^2\right).
\]
The source-residue mode at \(\rho_T\) obeys the exact, height-independent law
\[
 \frac{x_T(\tau)^r}{r!}
 \left|\partial_x^r\!\left(m e^{x/(\rho_T-1)}\right)
   \bigg|_{x=x_T(\tau)}\right|^2
 =
 |m|^2e^{2a\tau}
 \Pr\{\operatorname{Pois}(\tau)=r\}.
\]
Height has become observation time, horizontal displacement has become Lyapunov rate, and
derivative order carries the conserved packet.

This source-horizon theorem is the parent law.  Parabolic escape is its vertical-orbit
specialization; compact-open convergence is its fixed-time shadow; Ward quantization is its
static-mass shadow; Cayley/Li growth is its Lyapunov shadow; finite-jet blindness is its
fixed-order shadow; ridge tomography is its inverse map.

## Source mechanism

The Riemann zero is not primarily a point to be detected by a static positive scalar.  It is the
pole of the completed prime response, and therefore an initial condition for a canonical
Cayley evolution.

Let
\[
  \mathcal R(s)=\frac{\xi'(s)}{\xi(s)},\qquad
  E_x(s)=\exp\!\left(\frac{x}{s-1}\right).
\]
At a zero \(\rho\ne1\) of multiplicity \(m_\rho\),
\[
  \operatorname*{Res}_{s=\rho}\bigl(\mathcal R(s)E_x(s)\bigr)
  =m_\rho\exp\!\left(\frac{x}{\rho-1}\right).
\]
This coherent mode is itself the exact Poisson completion of the inverse Li--Cayley orbit.  With
\[
  w_\rho=1-\rho^{-1},\qquad a_\rho=w_\rho^{-1},
\]
one has
\[
 e^{x/(\rho-1)}
 =e^{-x}e^{a_\rho x}
 =\sum_{n\ge0}e^{-x}\frac{x^n}{n!}a_\rho^n.
\]
Thus discrete Li dynamics, continuous source evolution, and derivative-order transport are three
levels of one semigroup, not parallel criteria.

Writing
\[
  b_\rho=(\rho-1)^{-1},\qquad
  d_\rho=|b_\rho|^2,\qquad
  \kappa_\rho=|1+b_\rho|^2-1,
\]
the \(r\)-th derivative in evolution time is
\[
  \partial_x^r\operatorname*{Res}_{s=\rho}
     \bigl(\mathcal R(s)E_x(s)\bigr)
  =m_\rho b_\rho^r e^{b_\rho x}.
\]
Its factorially normalized energy is exactly
\[
  \frac{x^r}{r!}\left|m_\rho b_\rho^r e^{b_\rho x}\right|^2
  =m_\rho^2 e^{\kappa_\rho x}
    \Pr\{\operatorname{Pois}(d_\rho x)=r\}.
\]

At fixed height this is a conservation law in derivative-order space:

- packet velocity \(d_\rho=|\rho-1|^{-2}\);
- total exponential rate
  \[
    \kappa_\rho=(2\operatorname{Re}\rho-1)d_\rho;
  \]
- ridge/rate reconstruction
  \[
    \operatorname{Re}\rho=\frac12\left(1+\frac{\kappa_\rho}{d_\rho}\right),
    \qquad
    (\operatorname{Im}\rho)^2=
      \frac1{d_\rho}-\frac14\left(1-\frac{\kappa_\rho}{d_\rho}\right)^2.
  \]

Thus the critical line is not a coordinate inserted after the fact.  It is the neutral horizon of
the source \(s=1\): \(\kappa_\rho=0\).  Every strict-right zero is an exponentially unstable source
residue and every strict-left zero is its stable reflection.

## Why the corpus becomes shadows of this law

1. **Monodromy character.**  The strip-uniformizing character
   \(\exp(-2\pi i(\rho-\tfrac12))\) is a lossless log-polar coordinate for the same pole.
2. **Compact-open escape.**  For \(|\operatorname{Im}\rho|\to\infty\), \(d_\rho\to0\).  Fixed
   time collapses the packet, while the exact parabolic scale \(x=\tau/d_\rho\) restores it.
3. **Finite jets and differential matroids.**  They inspect bounded order before the migrating
   packet arrives; rational finite-divisor gauges therefore remain invisible.
4. **Trace-class energy.**  Reciprocal-square weighting is the small-\(d_\rho\) marginal and is
   noncoercive at the height boundary.
5. **Ward law.**  The source-weighted \(8\pi\) Ward index is the time-zero mass of the marked
   Cayley divisor.
6. **Cayley/Li visibility.**  Inverse radial powers are the discrete orbit whose Poisson
   completion is exactly the source residue mode; their growth is the same
   \(\kappa_\rho>0\) instability.
7. **Cayley--Fock exterior curvature.**  The adjacent-order determinant removes rotating phase
   while preserving \(d_\rho,\kappa_\rho\), every channel sign, and the complete packet mass.
8. **Gibbs/projective aperture.**  Zero-temperature free energy tropicalizes the family of
   positive rates and recovers its support edge while leaving the Gram radical unchanged.
9. **BV source dilation.**  Forward/inverse residues read the unsquared real character weight;
   the Cayley evolution additionally transports that residue through order space.
10. **Hypertranscendental Hurwitz family.**  Monodromy characters classify differential
    collisions, but the source residue evolution supplies the missing oriented dynamics; HGT
    independence and zero orientation are orthogonal projections of one pole character.

## Theorem package

1. Prove the universal source-horizon conservation law for arbitrary \(c,\rho,m\).
2. Prove the source inversion law converting reciprocal displacement into conjugate direct
   displacement at canonical time.
3. Prove the universal Poisson completion of every geometric Cayley orbit.
4. Prove the arithmetic source evolution
   \[
     (s-\rho)\mathcal R(s)E_x(s)\longrightarrow
       m_\rho e^{x/(\rho-1)}
   \]
   for every Xi zero, with no simplicity assumption.
5. Prove the full evolution-jet formula in \(x\).
6. Derive the exact parabolic escape-renormalization law as a corollary.
7. Identify these jets with the existing coherent exponential modes.
8. Import the existing Poisson conservation, phase-free exterior, strict sign, and
   ridge/rate reconstruction theorems.
9. Package the existing source-weighted Ward time-zero law, height--order visibility lower bound,
   exponential false-RH instability, and bounded-tower iff RH.
10. Add the compact-open Kolchin/Ward escape theorem: every holomorphic jet converges, the
   hypertranscendental stratum is unchanged, bounded windows lose the defect, yet Ward mass remains
   exactly \(8\pi\).
11. Add the strip-monodromy reconstruction and BV residue character coordinate only as charts of
   the pole, not as independent headlines.

## Paper question answered

**Question.** Where does an off-critical zero go when compact observation, trace weighting,
reflection symmetrization, and finite differential algebra all fail to see it?

**Answer.** It does not disappear.  Arithmetic residue transport sends it into a Poisson packet.
At fixed time its velocity tends to zero with height, producing every known blindness theorem.
At the unique inverse-drift scale \(x=\tau/d_\rho\), height cancels exactly and the packet reappears
as \(e^{(2\operatorname{Re}\rho-1)\tau}\operatorname{Pois}(\tau)\).  Co-moving observation
reconstructs the zero.  The one-sided orientation required for RH is precisely the surviving
Lyapunov exponent.  More universally, every source has a neutral horizon; the Riemann critical
line is the horizon selected by the arithmetic source at \(1\).

## Hostile gates

1. Reject if \(E_x(s)\) is only attached to zeros after the fact rather than multiplying the
   completed prime-source response before residues are taken.
2. Reject if the residue law assumes simple zeros.
3. Reject if Poisson conservation is presented as an asymptotic approximation; it must be exact.
4. Reject if the claimed universal law is stated only for the Riemann source rather than arbitrary
   source and divisor point.
5. Reject if it omits the exact canonical rescaling that cancels radial distance.
6. Reject if reconstruction loses \(\operatorname{Re}\rho\) or height.
7. Reject if the paper claims boundedness of the complete source tower; only the proved
   equivalence/instability may be stated.
8. Reject as headline if literature already uses this source-generated Poisson completion,
   neutral-horizon classification, and exact escape-renormalization law for meromorphic divisors.
9. Reject if HGT, Ward, Hilbert/projective, and compact-open results are listed without explicit
   maps to \(d_\rho,\kappa_\rho\), or the source residue.
10. Reject if the final narrative ends with an open conjecture.  The closed result is the
   escape-renormalization/conservation/reconstruction theorem; RH remains the application boundary.
