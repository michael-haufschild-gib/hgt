# Even \(K_{\mathbb R}\) structures tensor without parity loss

- **Status:** Formalized in Lean
- **Claim type:** THEOREM
- **Date:** 2026-07-25
- **Role:** Assemble rational archimedean and finite Bruhat factors

## Statement

If complex vector spaces \(M,N\) carry conjugate-linear involutions
\(\sigma_M^2=\sigma_N^2=1\), then
\[
  \sigma_{M\otimes N}(m\otimes n)
    =\sigma_M(m)\otimes\sigma_N(n)
\]
defines a conjugate-linear involution of \(M\otimes_{\mathbb C}N\).

## Proof

The displayed map is balanced because
\[
\begin{aligned}
 \sigma_M(zm)\otimes\sigma_N(n)
   &=\overline z\,\sigma_M(m)\otimes\sigma_N(n),\\
 \sigma_M(m)\otimes\sigma_N(zn)
   &=\sigma_M(m)\otimes\overline z\,\sigma_N(n).
\end{aligned}
\]
Both expressions agree in the tensor product. The tensor universal property therefore gives a
conjugate-linear map. On pure tensors its square is
\[
  \sigma_M^2(m)\otimes\sigma_N^2(n)=m\otimes n,
\]
and pure tensors generate the tensor product.

## Hostile checks

- Balance over \(\mathbb C\), not only \(\mathbb R\), is explicit.
- Result is for algebraic tensor products. Completed projective tensor topology remains a
  separate obligation.
- No numerical, arithmetic, positivity, spectrum, or RH premise occurs.

## Gates

- [x] Dependency-closed proof
- [x] Formalized in Lean; cached leaf builds and axiom audit passed
- [x] Applied to rational adelic Bruhat--Schwartz simple tensors

## Log

- 2026-07-25 — isolated to combine already formalized rational archimedean and finite local
  involutions.
- 2026-07-25 — formalized in `KRealTensorProduct.lean` and instantiated in
  `CCMRationalAdelicBruhatSimpleTensorReal.lean`. Axiom audit contains only `propext`,
  `Classical.choice`, and `Quot.sound`.
