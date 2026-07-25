# Kernel and cokernel descent in Deninger's \(K_{\mathbb R}\)

- **ID:** `kreal-kernel-cokernel-descent`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `kreal-quaternionic-ccm-cokernel` · categorical foundation
- **Statement:** kernels and algebraic cokernels of parity-preserving
  \(K_{\mathbb R}\)-morphisms inherit the same real/quaternionic square.

## Goal

Prove the categorical descent needed once the CCM restriction map has been enhanced to a genuine
\(K_{\mathbb R}\)-morphism.  This theorem isolates the formal quotient step from the arithmetic
problem of constructing the enhancement.

## Theorem

`[LITERATURE / PROVED HERE]` Fix \(p\in\{0,1\}\).  A parity-\(p\)
\(K_{\mathbb R}\)-space is a complex vector space \(V\) with a conjugate-linear map
\(\sigma_V\) satisfying
\[
  \sigma_V^2=(-1)^p.
\]
Let \(V,W\) be parity-\(p\) \(K_{\mathbb R}\)-spaces and let
\(f:V\to W\) be complex-linear with
\[
  \sigma_W f=f\sigma_V.                                  \tag{1}
\]
Then:

1. \(\ker f\) is \(\sigma_V\)-stable and the restriction of \(\sigma_V\) has square
   \((-1)^p\);
2. \(\operatorname{im}f\) is \(\sigma_W\)-stable;
3. the formula
   \[
     \overline{\sigma}_W([w])=[\sigma_W(w)]               \tag{2}
   \]
   is a well-defined conjugate-linear map on
   \(\operatorname{coker}f=W/\operatorname{im}f\);
4. \(\overline{\sigma}_W^2=(-1)^p\).

Consequently the category of parity-\(p\) \(K_{\mathbb R}\)-spaces has the ordinary algebraic
kernels and cokernels, created by forgetting to complex vector spaces.

## Proof

If \(v\in\ker f\), then by (1)
\[
  f(\sigma_Vv)=\sigma_W(fv)=0,
\]
so the kernel is stable.  Restricting \(\sigma_V^2=(-1)^p\) proves item 1.

If \(w=fv\), then
\[
  \sigma_Ww=\sigma_W(fv)=f(\sigma_Vv)\in\operatorname{im}f,
\]
proving item 2.  Therefore changing a representative \(w\) by an element of
\(\operatorname{im}f\) changes \(\sigma_Ww\) by another element of the image, so (2) is
well-defined.  Additivity and conjugate-linearity descend through the quotient.  Finally,
\[
  \overline{\sigma}_W^2([w])
    =[\sigma_W^2w]
    =[(-1)^pw]
    =(-1)^p[w].
\]

No analytic, arithmetic, positivity, or RH hypothesis is used.

## Exact CCM boundary

CCM define their cokernel by quotienting the target by the **closure** of the restriction image.
The algebraic theorem applies once that closed subspace is stable.  If the lifted
\(\sigma_W\) is a continuous homeomorphism and the image is stable, then its closure is stable
because homeomorphisms preserve closure.  Formalizing this topological strengthening is a
separate foundation; constructing the lifted \(\sigma\) on the CCM arrow remains the arithmetic
open core.

## Novelty audit

This is standard semilinear quotient algebra and is not claimed as new scientific knowledge.
Deninger explicitly describes \(K_{\mathbb R}\) as an abelian tensor category; the theorem
records the kernel/cokernel mechanism in the form needed by the CCM program.  Project search found
no existing formal definition or descent theorem.

Lean module:
`GaloisForLFunctions.RHTower.KRealKernelCokernel`.

Formal capstones:

- `KRealStructure.quotientSigma_sq`;
- `KRealStructure.kernelSigma_sq`;
- `KRealStructure.range_stable`;
- `KRealStructure.cokernel`;
- `KRealStructure.cokernel_sigma_mkQ`.

## Gates

- [x] 0 → 1 in-progress: exact categorical statement and CCM boundary identified
- [x] 1 → 2 fully-proven: complete proof above; no open dependency
- [x] 2 → 3 formalized: leaf build green; axiom audit contains only Lean foundational axioms;
  formal lint passes
- [ ] 3 → 4 publication-ready: not intended as a standalone new result

## Log

- 2026-07-25 — proved after the rational Morita-fiber construction separated source
  quaternionicity from cyclic descent.  No numerical evidence and no RH assumption used.
- 2026-07-25 — formalized in `KRealKernelCokernel.lean`; minimal
  `lake env lean GaloisForLFunctions/RHTower/KRealKernelCokernel.lean` passed; final
  `lake build GaloisForLFunctions.RHTower.KRealKernelCokernel` passed; formal lint passed.
