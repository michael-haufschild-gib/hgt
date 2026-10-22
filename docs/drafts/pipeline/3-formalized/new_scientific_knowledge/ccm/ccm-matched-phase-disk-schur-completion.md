# Matched CCM phase disk has a coefficient-faithful Schur completion

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseDiskSchurCompletion`.
This closes the local sign problem for one intact matched prime--polar cell after adding its exact
wall-chord complement. It does not yet transport the resulting non-summable reserve through the
global completed Gamma/Robin producer, so it is not an RH proof.

## New knowledge

Let `w_n` be the critical Mellin atom and let `C_n(xi)` and `S_n(xi)` be the corpus's matched even
cosine and odd sine phase profiles. Define the complementary cosine profile

\[
D_n(\xi)=\int_0^{\rho_n}2e^{\log(n)/2}\cosh(r/2)
  \bigl(1+\cos(2\pi r\xi)\bigr)\,dr.
\]

The radial density

\[
M_{n,r}(\xi)=2e^{\log(n)/2}
\begin{pmatrix}
\cosh(r/2)(1-\cos\theta) & \sinh(r/2)\sin\theta\\
\sinh(r/2)\sin\theta & \cosh(r/2)(1+\cos\theta)
\end{pmatrix},
\qquad \theta=2\pi r\xi,
\]

is positive semidefinite pointwise. Its determinant is

\[
4e^{\log n}\sin^2\theta\ge0,
\]

because `cosh^2-sinh^2=1`. Reusing HTGeometry's general theorem that entrywise integration
preserves matrix positivity gives

\[
\begin{pmatrix}C_n&S_n\\S_n&D_n\end{pmatrix}\succeq0.
\]

The exact matched-radius normalization gives `C_n+D_n=2w_n`. Therefore Lean proves both the Schur
minor inequality

\[
S_n(\xi)^2\le C_n(\xi)D_n(\xi)
\]

and the closed-disk law

\[
(C_n(\xi)-w_n)^2+S_n(\xi)^2\le w_n^2.
\]

This is a strict upgrade over separate first-moment bounds: it couples the oscillatory Suzuki
coordinate to two nonnegative even slacks with exact atom coefficient.

## Half-angle Schur diagonal

Test the integrated Gram matrix on the literal half-angle vector

\[
v_n(\xi)=
\begin{pmatrix}
\sin(\pi\log(n)\xi)\\-\cos(\pi\log(n)\xi)
\end{pmatrix}.
\]

Its quadratic form is exactly

\[
P_n(\xi)=w_n\bigl(1+\cos(2\pi\log(n)\xi)\bigr)
-\Bigl(\cos(2\pi\log(n)\xi)C_n(\xi)
+\sin(2\pi\log(n)\xi)S_n(\xi)\Bigr)\ge0.
\]

The bracket is precisely the real oriented symbol whose negative double is the intact actual-head
prime-minus-matched-polar cell. After integration against the literal Fourier density, Lean proves

\[
\text{matchedCell}_n(f)+R_n(f)=2\int P_n(\xi)|\widehat f(\xi)|^2\,d\xi\ge0.
\]

The reserve is source-faithful, not fitted:

\[
R_n(f)=4w_n\lVert f\rVert^2-w_nE_f(\log n),
\]

where `E_f` is the actual translation defect already occurring in the prime source.

## Higher principle

Earlier scalar sign and parity failures were shadows of compressing a two-channel positive Gram
density before rotating by the arithmetic phase. Correct order is:

1. retain cosine and sine channels as one PSD matrix density;
2. integrate using matched-radius mass normalization;
3. rotate by the literal prime half-angle;
4. take the physical Schur diagonal.

This simultaneously keeps the covariant Suzuki current and produces its exact positive diagonal.
The next hard problem is no longer local sign: transport the non-summable finite sum of reserves
`R_n(f)` into the actual completed Gamma/Robin/holonomy identity without coefficient replacement.
The reserve's exact `4w_n ||f||^2-w_nE_f(log n)` form supplies the required comparison target.

## Lean audit

- scratch conjecture/proof loop: passed;
- direct leaf check: passed;
- exact leaf-module build: passed;
- umbrella import: wired, not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
