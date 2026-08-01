# Skew-adjoint graph-core resolvent

- **ID:** `deninger-skew-adjoint-graph-core-resolvent`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Label:** `DAC_SKEW_ADJOINT_GRAPH_CORE_RESOLVENT`
- **Parent:** `deninger-hodge-schwartz-resolvent-core`
- **Statement:** an off-axis resolvent of a skew-adjoint generator is
  a continuous automorphism of every common smooth graph core built
  from closed operators that strongly commute with it.
- **Lean modules:**
  `GaloisForLFunctions.RHTower.DeningerSkewAdjointGraphCore` (`(4)`, `(5)`, `(3)`),
  `GaloisForLFunctions.RHTower.DeningerSkewAdjointResolventExists` (existence of `R_z`)

## Theorem

Let \(H\) be a complex Hilbert space and let \(A\) be skew-adjoint.
Let \((B_j)_{j\in J}\) be closed densely defined operators such that
every graph monomial \(B^\alpha\) commutes with the resolvent of \(A\)
on its natural domain.  Define
\[
  D_\infty
  =
  \bigcap_{\alpha}\operatorname{Dom}(B^\alpha)
  \cap
  \bigcap_{n\ge0}\operatorname{Dom}(A^n),                       \tag{1}
\]
with graph seminorms
\[
  p_{\alpha,n}(x)=\|B^\alpha A^n x\|.                           \tag{2}
\]

For every \(z\in\mathbb C\) with \(\operatorname{Re}z\ne0\),
\[
  A-z:D_\infty\longrightarrow D_\infty                         \tag{3}
\]
is a continuous linear automorphism.  Its inverse is the Hilbert
resolvent \(R_z=(A-z)^{-1}\), and
\[
  p_{\alpha,n}(R_zx)
  \le
  \frac1{|\operatorname{Re}z|}
  p_{\alpha,n}(x).                                              \tag{4}
\]

## Proof

`[PROVED HERE]`

Since \(A^*=-A\), the spectrum of \(A\) is contained in \(i\mathbb R\).
Hence \(z\) with \(\operatorname{Re}z\ne0\) belongs to the resolvent
set and the standard skew-adjoint resolvent estimate is
\[
  \|R_z\|\le|\operatorname{Re}z|^{-1}.                          \tag{5}
\]

Functional calculus gives \(A^nR_z=R_zA^n\) on
\(\operatorname{Dom}(A^n)\).  The strong-commutation hypothesis gives
the same identity for every \(B^\alpha\).  Therefore, for
\(x\in D_\infty\),
\[
\begin{aligned}
  p_{\alpha,n}(R_zx)
  &=\|B^\alpha A^nR_zx\|\\
  &=\|R_zB^\alpha A^nx\|\\
  &\le|\operatorname{Re}z|^{-1}p_{\alpha,n}(x),
\end{aligned}
\]
which proves `(4)` and shows \(R_zD_\infty\subset D_\infty\).

For \(y\in D_\infty\), put \(x=R_zy\).  Then \(x\in D_\infty\) and
\((A-z)x=y\), proving surjectivity.  Injectivity follows already on
\(\operatorname{Dom}A\).  The graph-seminorm estimates prove
continuity of the inverse, while continuity of \(A-z\) is immediate
from `(2)`.

## Arithmetic use

On harmonic degree one take \(B_j\) to be the source transverse,
fibred-cusp, and restricted-sum regularity operators.  The Hodge
Laplacian is used first to construct smooth harmonic representatives;
it need not commute with the conformal flow on every cochain degree.
Once the global Calderón--Green domain proves the required harmonic
strong commutation and identifies its source-smooth cohomology with a
dense subspace of this common graph core, off-axis source-resolvent
stability is automatic.

Thus the remaining arithmetic work is not a new spectral theorem.  It
is:

1. global domain construction;
2. commutation of flow with Green/Laplacian boundary conditions;
3. strict nuclear identification and density of the graph core in
   \(M_\zeta\).

## Formalized statement

`GaloisForLFunctions/RHTower/DeningerSkewAdjointGraphCore.lean`, over a complex inner-product
space:

- `DeningerSkewSymmetric A` : `⟪Ax, y⟫ = -⟪x, Ay⟫` for a linear map defined on a subspace;
- `deningerSkew_re_inner_self` : the numerical range is purely imaginary, `Re⟪Ax, x⟫ = 0`;
- `deningerSkew_lower_bound` : **`|Re z| ‖x‖ ≤ ‖(A - z)x‖`**.  This is the whole analytic content
  of `(5)`, and it is elementary: `Re⟪(A-z)x, x⟫ = -(Re z)‖x‖²`, then Cauchy--Schwarz;
- `deningerSkew_resolvent_norm_le` : `(5)` itself, `‖R_z y‖ ≤ |Re z|⁻¹ ‖y‖`, for any right
  inverse of `A - z`;
- `deningerGraphCore P = ⨅ i, (P i).domain` with `deningerGraphSeminorm` : the common smooth
  graph core `(1)` of a family of partially defined graph monomials, and the seminorms `(2)`;
- `DeningerGraphCommuting P R` : the strong-commutation hypothesis, that `R` preserves every
  monomial domain and commutes with the monomial there;
- `deningerGraphCore_map_mem` : `R_z D_∞ ⊆ D_∞`;
- `deningerGraphSeminorm_resolvent_le` : **`(4)`**, `p_{α,n}(R_z x) ≤ |Re z|⁻¹ p_{α,n}(x)`;
- `deningerCoreSub_bijective`, `deningerCoreEquiv` : **`(3)`**, the shifted generator is a linear
  automorphism of the core with the resolvent as inverse.

`GaloisForLFunctions/RHTower/DeningerSkewAdjointResolventExists.lean` supplies the input that the
card's proof takes from the spectral theorem — that `z` with `Re z ≠ 0` lies in the resolvent set
— and proves it directly, with no spectral theorem:

- `DeningerSkewAdjointPMap A := A.adjoint = -A` for a partially defined operator on a complex
  Hilbert space, with `deningerSkewAdjoint_skewSymmetric` giving skew-symmetry on the domain;
- `deningerShift A z = A - z` on `dom A`, with `deningerShift_injective`;
- `deningerShift_range_isClosed` : the range is closed.  The lower bound makes any sequence with
  convergent images a Cauchy sequence, and closedness of the graph of `A` supplies the limit;
- `deningerShift_range_orthogonal_eq_bot` : the range is dense.  A vector orthogonal to it lies in
  the domain of `A†` with `A†y = z̄y`; skew-adjointness turns this into `(A + z̄)y = 0`, and the
  lower bound at `-z̄` (whose real part is `-Re z ≠ 0`) forces `y = 0`;
- `deningerShift_bijective` : **`A - z : dom A → H` is a bijection** — the purely imaginary
  spectrum of a skew-adjoint operator;
- `deningerSkewAdjointResolvent`, `_spec`, `_norm_le` : the resolvent and its bound `(5)`.

Every step of the card's proof is formalized, including the step it delegates to Stone/spectral
theory.  The three items under "Arithmetic use" — global domain construction, commutation of the
flow with Green/Laplacian boundary conditions, and density of the graph core — are the card's own
separate conjectural inputs and are not part of this theorem.

### Verification

- Direct commands: `lake env lean` on both modules — pass with no errors and no warnings.
- Cached module build: `lake build
  GaloisForLFunctions.RHTower.DeningerSkewAdjointResolventExists` completes (`✔ [2393/2393]`).
- Scratch `#print axioms` on every headline declaration: only `propext`, `Classical.choice`,
  `Quot.sound`.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: exact graph-core statement
- [x] 1 → 2 fully-proven: complete proof
- [x] 2 → 3 formalized: `(3)`, `(4)`, `(5)`, and the existence of the off-axis resolvent
- [ ] 3 → 4 publication-ready: blocked on the three arithmetic inputs listed above

## References

- Stone's theorem and the spectral theorem for skew-adjoint
  generators.
- Christopher Deninger, *Arithmetic geometry and analysis on foliated
  spaces*, Theorem 4.1 and its use of Stone's theorem.
- Jesús A. Álvarez López, Yuri A. Kordyukov, Eric Leichtnam,
  *Analysis on Riemannian foliations of bounded geometry*,
  arXiv:1905.12912.
- Karsten Fritzsch, Daniel Grieser, Elmar Schrohe, *The Calderón
  Projector for Fibred Cusp Operators*, arXiv:2006.04645.

## Log

- 2026-07-27 — Extracted the abstract parameter-resolvent theorem.
  Global arithmetic source density and boundary-domain commutation
  remain separate conjectural inputs.
- 2026-08-01 — Formalized the theorem, including the spectral input.  `(5)` turned out not to
  need the spectral theorem at all in the form the card uses it: the lower bound
  `|Re z|‖x‖ ≤ ‖(A-z)x‖` follows from `Re⟪Ax,x⟫ = 0` and Cauchy--Schwarz, and the resolvent bound
  is then immediate for any right inverse.  What genuinely needed work was *existence* of that
  right inverse, so a second module proves it outright — closed range from the lower bound plus
  closedness of the graph, dense range from the adjoint identity `A†y = z̄y` and the lower bound
  at `-z̄`, then `Kᗮ = ⊥ ⇒ K = ⊤`.  Card moved to `3-formalized`.
