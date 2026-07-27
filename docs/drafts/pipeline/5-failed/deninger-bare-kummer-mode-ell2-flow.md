# Bare Kummer-mode \(\ell^2\) continuous flow

- **ID:** `deninger-bare-kummer-mode-ell2-flow`
- **Stage:** 5-failed
- **Type:** FALSIFIED GLOBAL-HILBERT ROUTE
- **Label:** `DAC_BARE_KUMMER_MODE_ELL2_FLOW_NO_GO`
- **Parent:** `deninger-affine-kummer-harmonic-fourier-modes`
- **Claim tested:** take the normalized local harmonic modes
  \(e_a\) as an orthonormal basis, complete them to
  \(\ell^2(V\setminus\{0\})\), and extend the centered rational-power
  shift \(e_a\mapsto e_{qa}\) directly to Deninger's continuous
  \(\mathbb R_{>0}\)-flow.

## No-go theorem

Let \(V\) be a nonzero rational vector space and define
\[
 U_q e_a=e_{qa},
 \qquad q\in\mathbb Q_{>0},\quad 0\ne a\in V.                  \tag{1}
\]

`[PROVED HERE] [DAC_BARE_KUMMER_MODE_ELL2_FLOW_NO_GO]`

The unitary representation `(1)` is not strongly continuous when
\(\mathbb Q_{>0}\) is given the subspace topology from
\(\mathbb R_{>0}\).  Consequently it has no strongly continuous
unitary extension to \(\mathbb R_{>0}\).

### Proof

Fix \(a\ne0\) and choose distinct rationals \(q_n\to1\).  Since
\(q_na\ne a\),
\[
 \langle U_{q_n}e_a,e_a\rangle=0
\]
and therefore
\[
 \|U_{q_n}e_a-e_a\|^2=2                                      \tag{2}
\]
for every \(n\).  Strong continuity at the identity would make the
left side tend to zero, contradicting `(2)`.

## Strongest positive survivor

`DAC_AFFINE_KUMMER_HARMONIC_FOURIER_MODES` remains valid locally:
the uncentered power pullback has norm weight \(q\), and the centered
map is the exact arithmetic shift.  What fails is discarding the
suspension-height variable before continuous induction.

The surviving construction is Deninger's/Paugam's smooth suspension:
\[
 \mathcal D(\mathcal H_{\mathrm{Kum}})
 =
 \Gamma^\infty
 \left(
 \mathcal H_{\mathrm{Kum}}\times\mathbb R_{>0}
 \to\mathbb R_{>0}
 \right)^{\mathbb Q_{>0}},                                    \tag{3}
\]
with flow acting by translation/dilation in the second variable.
The required Green carrier must be built on a smooth/nuclear subspace
of `(3)` before Hilbert completion.  Equivalently, a successful
completion must make the individual delta modes distributional rather
than Hilbert vectors.

## Exact new insight

Infinite Kummer rank avoids the finite-matrix dense-range theorem but
creates a new continuity constraint.  Arithmetic mode shifts and the
continuous Frobenius flow can coexist only after smooth induction
through suspension height; bare counting-measure \(\ell^2\) is too
discrete.

## Hostile audit

- No claim about the suspended smooth representation is falsified.
- The obstruction uses only a single basis vector and rational
  density.
- It does not use zeta zeros, RH, CCM, or numerical computation.
- Positive survivor points to an existing source operation rather
  than a zero-indexed replacement.

## Log

- 2026-07-27 — Proved strong-discontinuity of the bare Kummer
  permutation Hilbert space and retained smooth suspension induction
  as the required global carrier.
