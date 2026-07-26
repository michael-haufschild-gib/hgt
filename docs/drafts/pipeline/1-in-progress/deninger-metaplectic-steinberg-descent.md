# Deninger metaplectic--Steinberg descent

- **ID:** `deninger-metaplectic-steinberg-descent`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** `deninger-prime-holonomy-groupoid`
- **Source:** `docs/Deninger program.md` · `deninger-rectangular-quaternionic-hodge`
- **Statement:** The missing arithmetic coefficient twist is the metaplectic lift of the
  positive-similitude prime holonomy, formed before passing from universal Steinberg
  \(K_2\)-descent to its quaternionic representation.

## Motivation

Two independently forced pieces of the Deninger construction have the same square-root shape:

1. the moving rectangular prime map has determinant and metric weight \(p\), so its centered
   action is \(p^{-1/2}A_p\);
2. arithmetic \(H^1\) must be odd in \(K_{\mathbb R}\), hence its Hodge operator is anti-linear
   and squares to \(-1\).

For \(\tau=ir\), the positive similitude
\[
  A_q=\begin{pmatrix}q&0\\0&1\end{pmatrix}
\]
sends \(\tau\) to \(q\tau\).  Centering gives
\[
  q^{-1/2}A_q
   =\begin{pmatrix}\sqrt q&0\\0&1/\sqrt q\end{pmatrix}\in SL_2(\mathbb R).
\]
Square-root lifts of symplectic transformations are metaplectic.  Universal central extensions
of the relevant rank-two linear groups are controlled by Steinberg symbols and \(K_2\).  This
suggests that the missing half-density/quaternionic twist and the missing Steinberg relation are
not separate repairs.

## Exact frontier

- `[PAPER-PROVED]` Moving rectangular holonomy has weight one, forced coefficient \(1/r\), and
  forced centered exponent \(1/2\).
- `[PAPER-PROVED]` Its complexified tangent plane has a positive anti-linear
  \(\star^2=-1\) operator, preserved by centered holonomy.
- `[LITERATURE]` Kucharczyk--Scholze ask for a correction of their rational-Witt space obtained by
  freely adjoining the Steinberg relation in cohomology.
- `[LITERATURE]` Deninger's 2025 finite-flat/\(h\)/\(qfh\) sheafification still returns
  \(W_{\mathrm{rat}}\); stronger descent is required.
- `[LITERATURE]` Metaplectic/Weil representations arise by lifting projective symplectic actions
  to central extensions.  Matsumoto-style universal extensions are presented through Steinberg
  symbols.
- `[LITERATURE]` Brylinski--Deligne \(K_2\)-extensions yield metaplectic covers after local symbol
  pushout and split canonically over rational points in the global adelic theory.
- `[LITERATURE]` In the adelic Schrödinger model, the rational splitting is enforced by the theta
  distribution, the adelic product formula, and Poisson summation; local Maslov/Hilbert-symbol
  defects cancel globally.  Thus the splitting is arithmetic descent data, not evidence that all
  local twisting is trivial.
- `[OPEN]` No primary source identifies this lift with Deninger's desired arithmetic coefficient
  complex or proves its Xi comparison.

## Conjecture

`[CONJECTURE] [DAC_METAPLECTIC_STEINBERG_DESCENT]`:
the finite-correspondence realization of the corrected rational-Witt prime-holonomy groupoid
\(\mathcal G_{\mathbb Z}\) carries:

1. a rank-two oriented leafwise correspondence bundle \(T_{\mathrm{arith}}\) with positive
   similitude character
   \[
     \nu:\mathcal G_{\mathbb Z}\longrightarrow\mathbb R_{>0},
     \qquad \nu(F_p)=p;
   \]
2. a universal Steinberg central extension
   \[
     K_2^{\mathrm{St}}\longrightarrow
     \widetilde{\mathcal G}_{\mathbb Z}^{\mathrm{St}}
     \longrightarrow\mathcal G_{\mathbb Z},
   \]
   constructed before quotienting \(K_2^{\mathrm{St}}\) by any Hilbert-symbol character;
3. a metaplectic-similitude pushout of this extension whose centered action is
   \(\nu(g)^{-1/2}g\);
4. an adelic theta distribution invariant under the rational lift, with local factors equal to
   the prime and archimedean Weil representations and with global invariance proved by Poisson
   summation;
5. an associated complex quaternionic coefficient bundle
   \(\mathscr S_{\mathrm{arith}}\) whose local model is
   `deninger-rectangular-quaternionic-hodge`, whose Hodge operator squares to \(-1\), and which has
   no functorial real reduction;
6. a twisted leafwise de Rham complex
   \[
     \mathscr K_{\mathrm{arith}}
       =\Omega^\bullet_{\mathcal F}
          (Y_{\mathbb Z};\mathscr S_{\mathrm{arith}})
   \]
   whose Green projection is positive and whose flow commutes with Hodge after centering;
7. a dense cup-isometric, flow-equivariant comparison from its reduced degree-one cohomology to
   `DeningerArithmeticCompletedCohomology`, constructed before Xi divisor evaluation.

The existing determinant/Lefschetz and oriented-Hodge equivalence would then derive RH.

## Required proof obligations

1. Construct the universal extension on the actual rational-Witt finite-correspondence groupoid,
   not only on \(SL_2(F)\).
2. Prove the Steinberg relation is imposed before the metaplectic \(\mu_2\)-pushout.  A double
   cover alone sees only parity and cannot recover full additive descent.
3. Prove prime correspondences lift coherently and the local lift is the already proved centered
   rectangular Hodge map.
4. Construct the adelic theta section and derive its rational splitting from Poisson summation.
5. Prove the global bundle has no real reduction but has the required quaternionic structure.
6. Add the archimedean fixed-point germ and prove the \(\Gamma_{\mathbb R}\) Lefschetz term.
7. Construct the source comparison map and prove cup-isometry/dense range without spectral
   coordinates.

## Hostile audit

- `[PRIOR FAILED ROUTE]` Scalar theta convolution is closed: its reduced \(L^2\) cokernel is zero,
  while faithful positive Hilbertization of its analytic cokernel is RH-equivalent.
  **Required answer:** the present conjecture must construct genuinely non-scalar
  finite-correspondence/metaplectic cohomology with a geometric harmonic projection.  The adelic
  theta distribution may certify descent and Poisson gluing only; it may not be reused as a scalar
  \(L^2\) cokernel.
- `[OBJECTION]` The adelic metaplectic extension splits over rational points by reciprocity.
  **Required answer:** arithmetic twisting must live on the local/transversal groupoid; a global
  rational splitting must be derived from the theta distribution and Poisson summation and must
  express descent compatibility, not trivialize local holonomy.
- `[OBJECTION]` A Hilbert-symbol \(\mu_2\)-quotient loses most of \(K_2\).
  **Required answer:** retain universal Steinberg descent and push out only when constructing the
  quaternionic representation.
- `[OBJECTION]` Metaplectic representation theory alone does not produce Xi zeros or the explicit
  formula.
  **Required answer:** determinant/Lefschetz comparison and the source Green map remain separate
  mandatory gates.
- `[OBJECTION]` An untwisted global conjugation recreates the forbidden real cohomology.
  **Required answer:** transition data must be genuinely quaternionic and admit no real
  reduction.
- `[OBJECTION]` Postulating cup-isometric comparison is RH in disguise.
  **Required answer:** comparison must arise chainwise from finite correspondences and the Green
  projection.

## Verdict

`SECONDARY REALIZATION CANDIDATE`, not the active arithmetic-cohomology construction.  A
metaplectic pushout may explain the half-density/quaternionic representation only after the
source category has retained the full Steinberg and quadratic transfer data.  The active source
conjecture is `deninger-milnor-witt-hodge-realization`.  Falling back to scalar theta convolution
retires this candidate immediately.

## Log

- 2026-07-26 — conjecture created after local quaternionic Hodge theorem and 2025
  rational-Witt sheafification audit.
- 2026-07-26 — downgraded to secondary real-realization candidate after identifying arithmetic
  finite Milnor--Witt correspondences as the direct \(R\alpha_*\mathscr G\) source candidate.
