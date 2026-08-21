# Matched CCM source has a trace-free coherent-Fock tomography carrier

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseFockTomography`.
Every finite matched prime--polar packet is now an exact nonlinear reporter of one cross-prime
positive-semidefinite HilbertMetric kernel, with no local scalar Schur reserve inserted. This is
not yet an RH proof; cofinal control of the reporter remains open.

## Why this route was forced

The local matched phase Gram matrix has fixed trace `2 w_n`. Primewise Schur completion is positive,
but its center trace is nonsummable, and subtracting that trace reverses the Schur cone exactly.
Therefore positivity must occur after scalar trace removal and before any cofinal scalar readout.

Whole-corpus search produced four possible nonclassical carriers:

1. HTGeometry causal-Jordan fusion preserves exact visible signs, but still adds both scalar legs
   and therefore retains the divergent trace.
2. Finite interaction cohomology and finite split-formation parallax expose hidden directions, but
   the corpus's nonlocal--singular Riemann-source theorem rules out a finite-dimensional capstone.
3. Conditional-expectation covariance removes trace and creates PSD cross-correlations, but a
   linear covariance readout loses the literal oriented source coordinate.
4. HilbertMetric coherent-state kernels remove trace, retain nonlinear logarithmic coordinate
   recovery, and assemble arbitrary finite cross-prime packets positively. This route survives all
   three objections.

## Trace-free Bloch feature

For the matched cosine/sine profiles `C_n(xi), S_n(xi)` and critical Mellin weight `w_n`, define

\[
b_n(\xi)=(C_n(\xi)-w_n,\;S_n(\xi))\in\mathbb R^2.
\]

The phase-disk theorem becomes the exact Euclidean bound

\[
\lVert b_n(\xi)\rVert^2\le w_n^2.
\]

Unlike the local Schur diagonal, `b_n` contains no positive scalar trace. It is precisely the
projective/traceless part of the two-channel Gram disk.

## One cross-prime positive kernel

For an arbitrary finite index type `I`, a label map `n : I -> Nat`, and fixed `xi`, augment all
features `b_{n(i)}(xi)` by coordinate anchors `e_0,e_1`. Define

\[
K_{ab}(\xi)=\exp\langle x_a(\xi),x_b(\xi)\rangle,
\qquad x=(e_0,e_1,(b_{n(i)})_{i\in I}).
\]

HilbertMetric's universal exponential-inner-product theorem proves `K(xi)` positive semidefinite
for every finite packet. This is one coherent Gram object, not a sum of local PSD traces.

Its anchor entries recover both source coordinates exactly:

\[
\log K_{i,e_0}=C_{n(i)}-w_{n(i)},\qquad
\log K_{i,e_1}=S_{n(i)}.
\]

Moreover, every cross-atom covariance is forced by those anchor reporters:

\[
\log K_{ij}=
  \log K_{i,e_0}\log K_{j,e_0}+
  \log K_{i,e_1}\log K_{j,e_1}.
\]

Thus cross-prime entries are coefficient-determined rank-two logarithmic covariance, not an
arbitrary positive completion.

## Exact source tomography

Let `theta_n=2*pi*log(n)*xi`. The nonlinear kernel reporter

\[
T_n(\xi)=w_n\cos\theta_n+
  \cos\theta_n\log K_{n,e_0}+
  \sin\theta_n\log K_{n,e_1}
\]

is proved equal to the real oriented CCM phase symbol

\[
\cos\theta_n C_n(\xi)+\sin\theta_n S_n(\xi).
\]

Consequently, for every finite `F` and Sonin test `f`, Lean proves

\[
\operatorname{MatchedPrimePolarBlock}_F(f)
=-2\int_{\mathbb R}\left(\sum_{n\in F}T_n(\xi)\right)
  |\widehat f(\xi)|^2\,d\xi.
\]

This is literal coefficient landing from a PSD cross-prime kernel to the actual source block.
No RH premise, approximation, numerical step, added axiom, or target-fitted covariance appears.

## New route frontier

Classical scalar trace positivity is no longer the representation problem. The new frontier is:

- construct a nonproduct/cofinal topology for the coherent kernel packets;
- preserve positive finite restrictions and the two anchor sections;
- pass the logarithmic anchor reporter to the limit without a trace-class requirement;
- couple the resulting reporter to the completed source boundary.

Likely relevant corpus mechanisms are adaptive Mercer capacity, cofinal Cholesky frames, affine
prime-packet inverse limits, and nonlocal singular completion. Any candidate must preserve the
exact anchor-log identities above; ordinary weak convergence of matrix entries is insufficient
near zero.

## Lean audit

- scratch conjecture/proof loop: passed;
- direct leaf check: passed;
- exact leaf-module build: passed;
- umbrella import: wired, umbrella not built;
- capstone axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration in the new module.
