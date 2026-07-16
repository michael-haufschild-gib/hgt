# Passive positive-matrix spectral response gives block Hankel positivity

- **ID:** `passive-psd-matrix-density-spectral-hankel`
- **Status:** FORMALISED IN LEAN 4
- **Type:** reusable theorem / physics-to-observability bridge
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/PSDMatrixSpectralHankel.lean`
- **Scientific novelty:** not claimed; the value is a stronger Lean interface and direct hypothesis discharge

## Source relation

For a finite family of response channels, let

\[
  \rho(\omega)\in\operatorname{Mat}_{m\times m}(\mathbb R),\qquad
  \rho(\omega)\succeq0,
\]

be a positive-semidefinite matrix density and let `x(omega)` be any real spectral clock node.
Define

\[
  M_k^{ab}=\int \rho_{ab}(\omega)x(\omega)^k\,d\mu(\omega).
\]

The joint clock--channel Hankel block is

\[
  H_n[(i,a),(j,b)]=M_{i+j}^{ab}.
\]

At each spectral state, introduce the lift

\[
  B(\omega)_{a,(i,b)}=\delta_{ab}x(\omega)^i.
\]

Then the exact value relation is

\[
  H_n=\int B(\omega)^\top\rho(\omega)B(\omega)\,d\mu(\omega).
\]

Every pointwise integrand is positive semidefinite.  Therefore every finite block `H_n` is
positive semidefinite.  If every nonzero joint clock--channel vector has nonzero quadratic response
on a set of positive measure, then `H_n` is positive definite and `det H_n>0`.  Every single-channel
Hankel matrix is a principal submatrix and is consequently positive definite as well.

This is an observability statement.  The orders `i` are simultaneous reporter coordinates of one
static spectral object; no temporal evolution law is used.

## Physics provenance

Zhang--Monticone--Miller prove that the reciprocal part of the oscillator-strength density of the
electromagnetic scattering `T` matrix is a real-symmetric positive-semidefinite matrix
`X(omega) >= 0`, and represent the full response as a continuum of lossless matrix-valued
oscillators.  Their high- and low-frequency sum rules identify the total-strength and reciprocal
frequency moments.  See [Nature Communications 14, 7724
(2023)](https://www.nature.com/articles/s41467-023-43221-2), especially equations (3)--(6), and
[arXiv:2211.04457](https://arxiv.org/abs/2211.04457).

The same positive-matrix-density structure occurs in multi-field Kallen--Lehmann and EFT
positivity data; see Li--Xu--Yang--Zhang--Zhou,
[Physical Review Letters 127, 121601
(2021)](https://doi.org/10.1103/PhysRevLett.127.121601).

For electromagnetic response, choosing `x(omega)=omega^(-2)` gives a reciprocal-frequency matrix
moment tower.  The static and total-strength sum rules are its first visible values; the theorem
supplies the full block-Hankel positivity hierarchy whenever the remaining moments are integrable.

## Corpus gain

`ContinuumMatrixSpectralHankel` treated the rank-one density

\[
  \rho_{ab}(\omega)=g_a(\omega)g_b(\omega).
\]

An arbitrary positive matrix density can sometimes be reduced to that form only after enlarging
the latent space and supplying a measurable square-root or rank decomposition.  The new theorem
accepts `rho(omega) >= 0` directly, so physics-level passivity now discharges the positivity
hypothesis without an auxiliary factorization theorem.

Formal declarations:

- `integralMatrixKernel_quadratic_eq_integral`;
- `integralMatrixKernel_posSemidef`;
- `integralMatrixKernel_posDef_of_support`;
- `psdMatrixSpectralKernel_apply`;
- `psdMatrixSpectralBlockHankel_eq_integralMatrixKernel`;
- `psdMatrixSpectralBlockHankel_posSemidef`;
- `psdMatrixSpectralBlockHankel_posDef_of_jointSeparation`;
- `det_psdMatrixSpectralBlockHankel_pos_of_jointSeparation`;
- `det_momentHankelMatrix_psdMatrixSpectralChannelMoment_pos_of_jointSeparation`;
- `psdMatrixSpectralChannelMoment_not_fixedSpectralWidthLocalClosure`;
- the exact rank-one recovery theorems
  `psdMatrixSpectralMoment_rankOne_eq_continuumMatrixSpectralMoment` and
  `psdMatrixSpectralBlockHankel_rankOne_eq_continuumMatrixSpectralBlockHankel`.

The last boundary theorem says that a strictly observable channel cannot be locally reproduced by
any fixed finite oscillator palette.  It strengthens the general hypertranscendence program:
unbounded spectral observability is a positive, formal consequence of response structure even
before one proves that an analytic response is hypertranscendental.

## RH pressure test

This theorem does not itself prove the missing prime--Gamma source positivity.  It sharpens the
producer interface:

1. construct an actual positive-semidefinite matrix density from Euler/Gamma data;
2. identify one scalar channel with the normalized prime--archimedean moment sequence;
3. prove joint positive-measure separation.

Those three source statements would discharge the corresponding Hankel positivity and finite-width
obstructions automatically.  Merely postulating such a density would be another RH-strength
consumer and is not counted as progress.

## No-go and positive replacement

**No-go.** Causality or a scalar Herglotz sign alone does not provide the full mixed matrix moments
or strict block positivity, and cannot be used to infer the prime residual sign.

**Positive statement.** Pointwise matrix passivity plus integrability unconditionally yields all
finite block-Hankel semidefinite inequalities.  Positive-measure joint observability yields strict
determinants in every scalar channel and excludes every fixed finite spectral model.

## Verification

- exact target: `lake build +GaloisForLFunctions.HTGeometry.PSDMatrixSpectralHankel`
- direct file check: `lake env lean GaloisForLFunctions/HTGeometry/PSDMatrixSpectralHankel.lean`
- no numerical computation and no full build
