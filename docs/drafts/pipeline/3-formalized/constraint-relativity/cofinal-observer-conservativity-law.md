# Cofinal-observer conservativity law

- **ID:** `cofinal-observer-conservativity-law`
- **Stage:** 3-formalized
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [FORMALIZED IN LEAN]`
- **Novelty:** inverse-limit parent mathematics; first exact hostile test of finite-resource
  observer claims in this program.

## Structured setting

Let `mathscr L` be a category of complete separated decreasingly filtered topological vector
spaces

\[
 X\cong\varprojlim_N X/F^{N+1}X
 \tag{1}
\]

equipped with filtration-preserving differential `D`, filtration-preserving involution `tau`, and
a continuous filtration-raising prolongation `nabla`, with all morphisms preserving this data.
Write

\[
 Q_N(X)=X/F^{N+1}X.
\]

## Theorem

If `A subseteq mathbb N` is cofinal, the family `{Q_N}_{N in A}` is jointly conservative.
Conversely, in any tail-rich subcategory containing the objects below, no bounded family of
finite-resource observers is jointly conservative.

### Proof of sufficiency

Suppose `Q_N(f)` is an isomorphism for every `N in A`. Cofinality and completeness give

\[
 f\cong\varprojlim_{N\in A}Q_N(f).
\]

The inverse limit of the compatible inverse maps is an inverse to `f`. Compatibility with
`D,tau,nabla` and all framed data holds at every quotient and therefore in the limit. Thus `f` is
an isomorphism. QED.

### Proof of necessity

Let

\[
 X=\prod_{n\ge0}ke_n,
 \qquad F^NX=\prod_{n\ge N}ke_n,
\]

with

\[
 D=0,\qquad \nabla e_n=e_{n+1},\qquad \tau e_n=(-1)^ne_n.
\]

Then `tau nabla=-nabla tau`. Let a bounded observer family have largest index `M` and set
`K=F^{M+1}X`, with inherited filtration and pointing `e_{M+1}`. This object is nonzero, complete,
`nabla`-stable, and `tau`-stable. For every `N<=M`, `F^{N+1}K=K`, hence

\[
 Q_N(K)=0=Q_N(0).
\]

The family cannot distinguish `K` from zero and is not jointly conservative. QED.

## Exact interpretation

For the natural-number resource poset, a nonstabilizing tail requires a countably cofinal
observer atlas; no finite atlas suffices. If filtration stabilizes at `N_0`, one terminal observer
`Q_{N_0}` suffices. This separates stabilizing finite-law systems from genuinely nonstabilizing
pro-laws, but does not by itself construct an RH selection law.

## Lean-return note

No Lean work is authorized. Later formalization should begin only after choosing exact topological
and strictness hypotheses for inverse-limit reconstruction.

## Formalized companion

`cofinal-observer-conservativity-law-formalized.md` (same directory).
