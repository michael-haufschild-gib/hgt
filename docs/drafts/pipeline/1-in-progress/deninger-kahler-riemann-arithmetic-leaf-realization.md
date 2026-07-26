# Kähler--Riemann arithmetic leaf realization

- **ID:** `deninger-kahler-riemann-arithmetic-leaf-realization`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE
- **Label:** `DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION`
- **Parent:** `deninger-arithmetic-cohomology-construction`
- **Statement:** the coarse invariant arithmetic coefficient is the
  derived pushforward of a two-real-dimensional Kähler--Riemann leaf
  complex whose transverse flow conformally scales the leaf metric.

## Why this is the correct positivity gate

Deninger's formalism requires a positive Hodge star and
\(\Theta_1-\tfrac12\) skew-adjoint.  Deninger--Singhof prove both
conclusions for reduced cohomology once one has a dense-leaf
Kähler--Riemann foliation and a flow satisfying
\[
 (\phi^t)^*[\omega]=e^t[\omega].
\]
Therefore arithmetic positivity should not be imposed directly on a
zero-indexed Hilbert space.  It should be derived from a source leaf
metric.

Deninger's rational-Witt system is an approximation and its character
leaves are not known to be closed two-dimensional Riemannian leaves.  A
geometric refinement, or an equivalent sheaf-theoretic Hilbert complex,
is required.

## Conjecture

`[CONJECTURE] [DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION]`

There exists a pro-laminated arithmetic flow space
\[
 \alpha:S_{\mathrm{arith}}\longrightarrow X_W
\]
over Deninger's rational-Witt suspension with:

1. **Leaf dimension.**  Every finite stage is an oriented
   Kähler--Riemann lamination of complex leaf dimension one, with
   oriented one-dimensional transversal and dense generic leaf.
   The inverse system has unbounded harmonic dimension; the limit is not
   a single finite-harmonic Leichtnam model.
2. **Coefficient comparison.**  For the source coefficient of
   `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`,
   \[
   R\alpha_*\mathbb R_{\mathcal F}
   \simeq \mathscr A_X^\bullet                                      \tag{1}
   \]
   as multiplicative, Tate-graded, flow-equivariant complexes of
   complete locally convex sheaves.  An equivalent virtual leafwise
   Hilbert-complex realization is allowed; `(1)` is the invariant
   content.
3. **Reduced comparison.**  Maximal Hausdorff quotient commutes with the
   finite-stage limit and identifies
   \[
   \bar H^\bullet_{\mathcal F}(S_{\mathrm{arith}})
   \cong H^\bullet_{\mathrm{arith}}(X_W,\mathscr A_X).               \tag{2}
   \]
4. **Conformal flow.**  The transverse flow lifts to
   \(S_{\mathrm{arith}}\), maps leaves holomorphically to leaves, and
   scales the reduced Kähler class by
   \[
   (\phi^t)^*[\omega_{\mathcal F}]
   =e^t[\omega_{\mathcal F}].                                      \tag{3}
   \]
5. **Arithmetic orbits.**  Primitive compact orbits are the prime
   packets, have length \(\log p\), and their oriented linearized return
   maps agree with the MW residue/Gysin orientation.
6. **Archimedean boundary.**  The real signature class is the leafwise
   fundamental orientation and supplies
   \(H^2_{\mathrm{arith}}\cong\mathbb R(-1)\).
7. **Hilbert regularity.**  Leafwise Laplacians are essentially
   self-adjoint on a common core, harmonic projectors are compatible
   across stages, and the centered flow is strongly continuous on the
   harmonic Hilbert completion.
8. **Pro-nuclear trace.**  Test-function-smoothed flow operators are
   nuclear at the limit and finite-stage Lefschetz distributions converge
   in \(\mathcal D'(\mathbb R)\), while reduced \(H^1\) is
   infinite-dimensional.

## Forced consequences

From clauses 1, 3, 4, and 7,
`DAC_KAHLER_RIEMANN_FLOW_PURITY` gives
\[
 \Theta_n=\frac n2+S_n,\qquad S_n^*=-S_n.
\]
Clause 5 supplies the geometric input for a Guillemin--Sternberg/Deninger
distributional Lefschetz formula.  Clauses 2 and 6 transport cup,
trace, and Poincaré duality to the three-term arithmetic complex.

Thus construction of this one object closes the source Hodge positivity
gate; it does not by itself identify the spectrum with zeta zeros.

## Construction program

1. Refine each finite pro-Stein character chart by a one-complex-dimensional
   leaf chart carrying the logarithmic Kummer differential.
2. Glue charts through rational-Witt finite correspondences and twisted MW
   residue maps.
3. Construct a bundle-like metric whose leafwise area form represents the
   Tate orientation.
4. Prove transition maps are leafwise holomorphic and preserve the metric
   up to the Frobenius scale.
5. Establish `(1)` by the same quotient-adapted hypercover used for
   `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`.
6. Prove closed-range/reduced Hodge decomposition stagewise and then the
   limit theorem in clause 3.
7. Identify prime return maps and the archimedean orientation before any
   comparison with the explicit formula.

## Falsifiers

- A leaf model of complex dimension other than one gives the wrong
  arithmetic cohomological dimension.
- A metric defined using zeta zeros, Xi, Weil positivity, or RH is
  circular.
- If `(3)` has scale \(e^{ct}\) with \(c\ne1\), middle purity is on
  \(\operatorname{Re}s=c/2\), not the critical line.
- If the generic leaf is not dense, top reduced cohomology and
  Poincaré duality need not have the required one-dimensional form.
- Formal Hodge star without closed reduced differentials does not give
  the needed Hilbert-space adjoint theorem.
- A single finite-dimensional harmonic sector is ruled out by
  `DAC_SINGLE_FINITE_TRANSVERSE_LAMINATION_NO_GO`.

## Current status

- Kähler--Riemann Hodge decomposition, Poincaré duality, polarization,
  and conformal-flow purity: literature/paper-proved.
- Abstract three-term purity implication: paper-proved; Lean written,
  direct check deferred during external build saturation.
- Arithmetic leaf refinement, coefficient pushforward comparison,
  bundle-like conformal metric, and reduced limit theorem: open.

**Verdict:** `ACTIVE SOURCE CONJECTURE; EXACT HODGE/POSITIVITY
CONSTRUCTION GATE`.

## Log

- 2026-07-26 — Created after extracting Deninger--Singhof Proposition
  4.6 and separating geometric positivity from zero-defined Hilbert
  targets.
