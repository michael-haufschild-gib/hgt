# Completed prime--Gamma moving complex Hankel surface

- **ID:** `completed-prime-gamma-moving-complex-hankel`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaMovingComplexHankel.lean`

## Statement

For the moving completed moment germ `G_sigma`, retain the full coefficients

\[
  \widehat c_k(\sigma)=\frac{G_\sigma^{(2k)}(0)}{(2k)!}
\]

and form their finite Hankel determinant `widehatDelta_n`.  Lean proves

\[
  \widehat\Delta_n(1-\sigma)=\widehat\Delta_n(\sigma)
\]

and the no-loss center specialization

\[
  \widehat\Delta_n(1/2)=
  \left(\det(\texttt{primeArchSourceMomentHankelMatrix }n):\mathbb C\right).
\]

The file also defines the explicit paper family

\[
  c_k(\sigma)=
  \frac{(-1)^k}{(2k+1)!}
  \left(\frac{\xi'}{\xi}\right)^{(2k+1)}(\sigma)
\]

and its determinant `Delta_n`.  Unconditionally,

\[
  \Delta_n(1-\sigma)=\Delta_n(\sigma),
\]

and `Delta_n` is holomorphic at every point where `xi` is nonzero.
Lean also proves the exact affine chain-rule bridge

\[
  \widehat c_k(1/2)=c_k(1/2),
  \qquad
  \widehat\Delta_n(1/2)=\Delta_n(1/2),
\]

and Schwarz reality

\[
  \Delta_n(\overline\sigma)=\overline{\Delta_n(\sigma)}.
\]

Hence `Delta_n(x)` is real for every real `x`.

## Formal declarations

- `complexAnalyticTraceMoment`;
- `completedMovingComplexMoment`;
- `completedMovingComplexHankelMatrix`;
- `completedMovingComplexHankelDet`;
- `completedMovingComplexMoment_one_sub`;
- `completedMovingComplexHankelDet_one_sub`;
- `completedMovingComplexMoment_one_half`;
- `completedMovingComplexHankelMatrix_one_half`;
- `completedMovingComplexHankelDet_one_half`;
- `completedOddLogDerivMoment`;
- `completedOddLogDerivHankelMatrix`;
- `completedOddLogDerivHankelDet`;
- `completedOddLogDerivMoment_one_sub`;
- `completedOddLogDerivHankelDet_one_sub`;
- `analyticAt_completedOddLogDerivMoment`;
- `analyticAt_completedOddLogDerivHankelDet`.
- `completedMovingComplexMoment_eq_completedOddLogDerivMoment_one_half`;
- `completedMovingComplexHankelDet_eq_completedOddLogDerivHankelDet_one_half`;
- `completedOddLogDerivMoment_conj`;
- `completedOddLogDerivHankelDet_conj`;
- `completedOddLogDerivHankelDet_ofReal_im`.
- `completedOddLogDerivHankelDet_central_order_even`.

## Top-down consequence

The earlier real-valued moving determinant discarded the complex function required by
`analyticOrderAt`.  The explicit determinant now supplies that function.  Therefore the far-right
route can ask for exclusion of odd-order real zeros rather than exclusion of all zeros.

The affine center identification between the explicit logarithmic-derivative family and the
full-germ family is now formalized.  The source-side exclusion of noncentral odd-order zeros and
the abstract even-order sign-transport lemma remain tracked by
`completed-prime-gamma-complex-hankel-parity-transfer`.

## Gates

- [x] full complex coefficient matrix and determinant
- [x] exact functional-equation reflection
- [x] exact central scalar-extension identity for the moving germ family
- [x] explicit logarithmic-derivative determinant
- [x] holomorphy away from the Xi divisor
- [x] exact affine center identification of the two complex determinant families
- [x] Schwarz reality and real-axis reality of the explicit determinant
- [x] automatic even order at the functional-equation fixed point
- [x] imported by the RHTower umbrella
- [x] no placeholders or project axioms
