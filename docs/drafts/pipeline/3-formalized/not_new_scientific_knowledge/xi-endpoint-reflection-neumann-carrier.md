# Xi Endpoint Reflection Neumann Carrier

- **ID:** xi-endpoint-reflection-neumann-carrier
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Connes prime--archimedean endpoint route
- **Statement:** The completed endpoint source forces the raw reciprocal Xi divisor into a strict unit ball, so the critical-line reflection channel is an absolutely convergent Neumann series in the conjugate raw coordinate and its global endpoint cross trace is an all-order holomorphic reciprocal-power trace series.

## Goal

Replace the endpoint's apparently independent reflected channel by a cofinal analytic readout of one raw reciprocal channel.  This gives a concrete all-order carrier on which a source-side positivity or norm argument can act.  The theorem does not assert that the resulting reflection defect vanishes.

## Theorem

Let
\[
C=-\Re\frac{(\log \Xi_C)'(i/2)}{i/2},\qquad
H=\sum_{\rho}\left|\frac1\rho\right|^2,
\]
where the sum is over the multiplicity-exact nontrivial Xi divisor, and let
\[
E=\sum_{\rho}
\left|\frac1\rho-\frac1{1-\overline\rho}\right|^2.
\]
Then, unconditionally,
\[
C=2+\gamma-\log(4\pi),\qquad
0<C<\frac12,
\]
\[
E\le \frac{C^2}{1-C}<C,
\qquad
C\le H<\frac32C<\frac34.
\]
Consequently every raw reciprocal coordinate lies in the open unit disk and
\[
\frac1{1-\overline\rho}
=-\sum_{n\ge1}\overline{\rho^{-1}}^{,n}
\]
absolutely.  If
\[
T_k=\sum_\rho \rho^{-k},\qquad k\ge2,
\]
then the double series is absolutely summable and
\[
-\frac{(\log\Xi_C)'(i/2)}{i/2}
=-\sum_{n\ge0}T_{n+2},
\qquad
C=-\sum_{n\ge0}\Re T_{n+2}.
\]

The sharp endpoint equality remains
\[
H=C\iff E=0\iff \mathrm{RH}.
\]

## Proof

The functional equation and Schwarz symmetry identify the endpoint cross term with
\[
\frac1\rho\overline{\frac1{1-\overline\rho}}
=-\frac{\rho^{-2}}{1-\rho^{-1}}.
\]
The endpoint polarization identity gives
\[
E=2(H-C).
\]
The critical-strip pointwise estimate and the completed endpoint value give
\[
E\le\frac{C^2}{1-C}.
\]
The completed functional equation transports the exact Laurent constant at one to zero, yielding
\(C=2+\gamma-\log(4\pi)\).  Elementary rational bounds give \(0<C<1/2\), hence the strict defect
factor \(C/(1-C)<1\) and \(H<3C/2<3/4\).

Since each \(|\rho^{-1}|^2\) is bounded by the total mass \(H\), every \(|\rho^{-1}|<1\), and the
pointwise Möbius identity expands geometrically.  The uniform bound \(|\rho^{-1}|<9/10\) majorizes
the double family by
\[
\left(\frac9{10}\right)^n|\rho^{-1}|^2.
\]
Tonelli therefore permits interchange of the zero and power sums.  The centered relative-resolvent
identity identifies the resulting endpoint cross trace with
\(- (\log\Xi_C)'(i/2)/(i/2)\), proving the complex and real source formulas.

## Formal certificate

- `xiEndpointCompletedCurvature_lt_one_half`
- `xiEndpointReflectionDefectEnergy_lt_endpointCurvature`
- `xiRawReciprocalHermitianMass_lt_three_fourths`
- `hasSum_xiRawReciprocalCoordinate_lineConj_neumann`
- `hasSum_xiEndpointCrossTrace_allOrder`
- `hasSum_completedEndpointLogDeriv_holomorphicTraces`
- `hasSum_xiEndpointCompletedCurvature_holomorphicTraces`
- `primeArchConnesReflectionMain`

Primary modules:

- `formal/GaloisForLFunctions/RHTower/XiEndpointReflectionNeumannCarrier.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchConnesReflectionMain.lean`

## Remaining RH-bearing theorem

The Neumann reconstruction carries the reflected endpoint channel cofinally, but it does not make
the reflection fixed.  A proof must now establish one of the equivalent sharp statements
\[
H\le C,
\qquad E=0,
\qquad
\text{all normalized prime--archimedean Hankel forms are positive}.
\]
The quantitative result supplies the strict initial estimate \(E<C\); the missing step is a
source-side mechanism that propagates this strict contraction through the full all-order trace
carrier and forces its antisymmetric component to vanish.

## Gates

- [x] 0 → 1 in-progress: exact endpoint carrier and attack identified
- [x] 1 → 2 fully-proven: complete unconditional proof above
- [x] 2 → 3 formalized: primary module builds without placeholders
- [ ] 3 → 4 publication-ready: novelty and literature status intentionally unasserted here
