# Even Real algebra involutions act functorially on cyclic words

- **Status:** Formalized in Lean
- **Claim type:** THEOREM
- **Date:** 2026-07-25
- **Role:** Algebraic cyclic-degree bridge for CCM Real equivariance

## Statement

Let \(A\) be a complex unital algebra and let
\(\sigma:A\to A\) be conjugate-linear with
\[
  \sigma^2=1,\qquad \sigma(1)=1,\qquad
  \sigma(ab)=\sigma(a)\sigma(b).
\]
Apply \(\sigma\) componentwise to every cyclic word
\((a_0,\ldots,a_n)\). Then componentwise \(\sigma\):

1. squares to the identity;
2. commutes with every internal face, which replaces \(a_i,a_{i+1}\) by
   \(a_i a_{i+1}\);
3. commutes with the last cyclic face, which replaces \(a_n,a_0\) by
   \(a_na_0\);
4. commutes with every degeneracy, which inserts \(1\);
5. commutes with cyclic rotation.

Consequently it defines an even Real involution of the algebraic cyclic module
\(A^\natural\). Every equivariant unital algebra morphism induces an equivariant cyclic
morphism.

## Proof

Componentwise involutivity is \(\sigma^2=1\). Each internal or last face uses one
multiplication, so compatibility is exactly
\(\sigma(ab)=\sigma(a)\sigma(b)\). Each degeneracy uses one inserted unit, so compatibility
is exactly \(\sigma(1)=1\). Rotation only permutes components and therefore commutes with
componentwise application. Additivity and conjugate-linearity descend from the tensor
universal property.

For an equivariant unital algebra morphism \(f:A\to B\), its degree-\(n\) cyclic map is
\(f^{\otimes(n+1)}\). Componentwise equivariance gives
\[
  f^{\otimes(n+1)}\sigma_A^{\otimes(n+1)}
   =\sigma_B^{\otimes(n+1)}f^{\otimes(n+1)}
\]
on pure tensors, hence on the whole tensor product.

## Hostile checks

- This theorem proves cyclic-degree propagation only; it does not construct any completion.
- Multiplicativity is order-preserving. An anti-automorphism would require a reflection of
  cyclic order and is not covered.
- Tensor-product conjugate-linearity is used only through its universal property; no
  finite-dimensional assumption occurs.
- No arithmetic, trace, positivity, spectrum, or RH premise occurs.

## Gates

- [x] Dependency-closed proof
- [x] Hostile variance/order audit
- [x] Formalized in Lean; cached leaf builds and axiom audit passed
- [ ] Instantiated for rational CCM completed cyclic modules

## Log

- 2026-07-25 — isolated from the analytic CCM Real-descent proof after confirming mathlib has
  simplicial infrastructure but no cyclic-module implementation. No numerical evidence used.
- 2026-07-25 — formalized generically in `KRealCyclicWord.lean` and instantiated for the
  finite-support rational CCM crossed product in `CCMRationalCyclicRealCore.lean`. Axiom audit
  contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Lean formalization

Modules:

- `GaloisForLFunctions.RHTower.KRealCyclicWord`;
- `GaloisForLFunctions.RHTower.CCM.CCMRationalCyclicRealCore`.

Formal capstones:

- `KRealAlgebraStructure.cyclicWordSigma_sq`;
- `KRealAlgebraStructure.cyclicWordSigma_rotate`;
- `KRealAlgebraStructure.cyclicWordSigma_internalFace`;
- `KRealAlgebraStructure.cyclicWordSigma_lastFace`;
- `KRealAlgebraStructure.cyclicWordSigma_degeneracy`;
- `ccmRationalCyclicWordRealStructure_sq`;
- `ccmRationalCyclicWordRealStructure_rotate`;
- `ccmRationalCyclicWordRealStructure_internalFace`;
- `ccmRationalCyclicWordRealStructure_degeneracy`.
