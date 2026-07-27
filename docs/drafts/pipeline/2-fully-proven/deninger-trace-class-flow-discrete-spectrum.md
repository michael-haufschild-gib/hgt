# Trace-class unitary flow has discrete faithful spectrum

- **ID:** `deninger-trace-class-flow-discrete-spectrum`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_TRACE_CLASS_UNITARY_FLOW_DISCRETE_SPECTRUM`
- **Parent:** `deninger-arithmetic-lefschetz-determinant-comparison`
- **Statement:** trace-class smoothing of a strongly continuous
  unitary flow forces compact resolvent and makes its distribution
  character a faithful record of spectral multiplicities.

## Theorem

Let \(U_t\) be a strongly continuous unitary group on a separable
Hilbert space \(H\), with
\[
 U_t=e^{itA}
\]
for the self-adjoint Stone generator \(A\).  For
\(\varphi\in C_c^\infty(\mathbb R)\), set
\[
 K_\varphi=\int_{\mathbb R}\varphi(t)U_t\,dt.                      \tag{1}
\]

`[PROVED HERE] [DAC_TRACE_CLASS_UNITARY_FLOW_DISCRETE_SPECTRUM]`

If every \(K_\varphi\) is trace class, then:

1. every bounded spectral interval of \(A\) has finite-dimensional
   spectral projection;
2. \(A\) has pure discrete real spectrum with finite multiplicities
   and no finite accumulation point;
3. \((A-i)^{-1}\) is compact;
4. for the spectral multiset \(\{(\lambda_j,m_j)\}\),
   \[
     \operatorname{Tr}K_\varphi
       =\sum_jm_j\,\widehat\varphi(-\lambda_j),                     \tag{2}
   \]
   with absolute convergence;
5. the map
   \(\varphi\mapsto\operatorname{Tr}K_\varphi\) is a distribution,
   the multiplicity measure
   \[
     \nu_A=\sum_jm_j\delta_{\lambda_j}                              \tag{3}
   \]
   is tempered, and this distribution determines \(\nu_A\) uniquely.

It is enough to assume `(1)` trace class for test functions supported
in positive time.  Indeed, translating any test function far enough to
positive time multiplies its operator by one unitary \(U_T\), which
preserves trace class.

## Proof

By the spectral theorem,
\[
 K_\varphi=\widehat\varphi(-A).                                    \tag{4}
\]
Fix \(\lambda_0\in\mathbb R\).  Choose a compactly supported smooth
\(\varphi\) with
\(\widehat\varphi(-\lambda_0)\ne0\).  Continuity gives a neighborhood
\(I\) of \(\lambda_0\) and \(c>0\) such that
\[
 |\widehat\varphi(-\lambda)|\ge c\qquad(\lambda\in I).
\]
On the spectral subspace \(E_A(I)H\), the compact operator
\(K_\varphi\) is bounded below by \(c\).  A compact operator cannot be
bounded below on an infinite-dimensional subspace, so
\(E_A(I)H\) is finite-dimensional.

Every compact spectral interval has a finite subcover by such
neighborhoods, proving clause 1.  The spectral theorem then gives
clauses 2 and 3.  In an orthonormal eigenbasis, `(4)` is diagonal.
Trace-class summability gives `(2)`.

It remains to justify the topological assertion in clause 5 rather
than silently assuming it.  For a fixed compact interval \(J\), let
\(\mathcal D_J\) be the Fréchet space of smooth functions supported in
\(J\).  The linear map
\[
 \mathcal D_J\longrightarrow\mathcal S_1(H),\qquad
 \varphi\longmapsto K_\varphi
\]
has closed graph: convergence in trace norm implies convergence in
operator norm, while convergence in \(\mathcal D_J\) implies
\[
 \|K_{\varphi_n}-K_\varphi\|
 \leq \|\varphi_n-\varphi\|_{L^1}\longrightarrow0.
\]
The closed graph theorem therefore makes this map continuous.
Taking traces and using the strict inductive-limit topology of
\(\mathcal D(\mathbb R)\) proves that
\(\varphi\mapsto\operatorname{Tr}K_\varphi\) is a distribution.

This continuity also forces polynomial spectral growth.  Choose
\(\varphi_0\in\mathcal D_J\) whose Fourier transform has absolute
value at least \(c>0\) on a neighborhood of zero.  Modulation
\(\varphi_x(t)=e^{-ixt}\varphi_0(t)\) moves that neighborhood to one
centered at \(x\), while every fixed finite family of
\(\mathcal D_J\)-seminorms of \(\varphi_x\) grows at most polynomially
in \(|x|\).  Continuity into trace class and the diagonal formula
`(4)` consequently give
\[
 \nu_A([x-\varepsilon,x+\varepsilon])
   \leq C(1+|x|)^N
\]
for fixed \(\varepsilon,C,N>0\).  Thus \(\nu_A\) is tempered.  Formula
`(2)` is its Fourier-transform pairing, so injectivity of the Fourier
transform on tempered distributions proves uniqueness in clause 5.

For the positive-time reduction, if
\(\psi(t)=\varphi(t-T)\), then
\[
 K_\psi=U_TK_\varphi.
\]
Choose \(T\) so that \(\operatorname{supp}\psi\subset(0,\infty)\).

## Deninger specialization

If source Hodge purity gives
\[
 \Theta_1=\tfrac12+iA,
\]
then
\[
 e^{-t/2}e^{t\Theta_1}=e^{itA}.
\]
Trace-class smoothing of \(e^{t\Theta_1}\) on positive time is
equivalent, after multiplying test functions by \(e^{t/2}\), to the
hypothesis above.  Therefore source Hodge unitarity plus the
cohomological trace-class theorem automatically supplies discrete
finite-multiplicity middle spectrum and a faithful spectral character.

This does not construct the flow, prove trace class, or identify its
character with the prime/archimedean Lefschetz distribution.

## Gates

- [x] complete paper proof
- [ ] Lean formalization of Stone/spectral-theorem specialization
- [ ] application to the constructed arithmetic flow

## References

- M. H. Stone, spectral theorem for strongly continuous unitary
  groups.
- Michael Reed and Barry Simon, *Methods of Modern Mathematical
  Physics I*, functional calculus and compact resolvent.

## Log

- 2026-07-26 — Removed faithful discrete spectrum as an independent
  determinant conjecture once Hodge unitarity and smoothed trace class
  hold.
