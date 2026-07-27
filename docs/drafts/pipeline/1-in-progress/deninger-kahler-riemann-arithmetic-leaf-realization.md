# Kähler--Riemann arithmetic leaf realization

- **ID:** `deninger-kahler-riemann-arithmetic-leaf-realization`
- **Stage:** 1-in-progress
- **Type:** SOURCE CONJECTURE
- **Label:** `DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION`
- **Parent:** `deninger-arithmetic-cohomology-construction`
- **Statement:** the coarse invariant arithmetic coefficient is the
  derived pushforward of a complex
  two-real-dimensional Kähler--Riemann leaf complex whose transverse
  flow conformally scales the leaf metric and whose degree-one
  cohomology is odd in \(K_{\mathbb R}\); its all-number-fields
  extension is genuinely quaternionically twisted.

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

Deninger's no-real-coefficients theorem adds a non-negotiable
full-theory constraint: ordinary complexified real leafwise cohomology
cannot be the arithmetic \(H^1\) functorially for all number fields.
For the single \(\mathbb Q\) object, an additional real form is not
excluded; what is mandatory is an odd \(K_{\mathbb R}\) operator
\(J^2=-1\).  The all-number-fields extension must carry genuinely
quaternionic descent with no functorial real reduction.

## Exact twisted analytic interface

Benameur--Heitsch's twisted harmonic-signature theorem applies to an
oriented even-dimensional Riemannian foliation of a compact manifold
with a leafwise flat complex bundle \(E\) carrying a nondegenerate
Hermitian metric preserved by the leafwise flat connection.  Their
leafwise Hodge lemma identifies harmonic forms with reduced
\(L^2\)-cohomology.  Their transverse regularity theorem says that the
harmonic projection on the homotopy groupoid is transversely smooth
when leafwise parallel translation is bounded; this holds in particular
when the preserved Hermitian metric is positive definite.

This theorem supplies the analytic Hodge decomposition and smooth
harmonic projector once the arithmetic coefficient exists.  It does
not construct that coefficient, the rational-Witt leaf refinement, the
conformal flow, comparison `(1)`, or the Poisson--zeta cup pairing.
Those remain source obligations below.

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
2. **Arithmetic-total comparison.**  Let
   \(\mathscr A_{\mathrm{arith}}\) be the sheaf-level
   generic/prime Rost--Schmid localization totalization of
   `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`, including its real
   orientation boundary.  Then
   \[
   R\alpha_*\Omega^\bullet_{\mathcal F}
      (\mathscr S_{\mathrm{arith}})
   \simeq \mathscr A_{\mathrm{arith}}^\bullet                       \tag{1}
   \]
   as multiplicative, Tate-graded, flow-equivariant complexes of
   complete locally convex sheaves.  An equivalent virtual leafwise
   Hilbert-complex realization is allowed; `(1)` is the invariant
   content.  On the logarithmic Kummer summand, the locally convex
   topology restricts to
   `DAC_ADELIC_L1_L2_ROST_SCHMID_HODGE_COEFFICIENT`; bare adelic
   \(L^2\) is excluded.
3. **Coefficient parity.**
   \(\mathscr S_{\mathrm{arith}}\) is a leafwise flat positive Hermitian
   complex local system whose degree-one harmonic cohomology has a
   parallel, antiunitary, anti-linear operator \(J\) satisfying
   \(J^2=-1\).  Thus it is odd in \(K_{\mathbb R}\).  With the convention
   \[
     \psi_E(u,v)=-h_E(u,Jv),
   \]
   \(\psi_E\) is complex-bilinear alternating and
   \(\psi_E(v,Jv)=h_E(v,v)>0\).  Its chartwise form is
   `DAC_RECTANGULAR_QUATERNIONIC_HODGE`; the derived cup product uses
   the coefficient's internal parity in its Koszul sign.  For the
   all-number-fields extension, the transition datum has no functorial
   real reduction.  The constant and Arakelov degree lines are even
   \(K_{\mathbb R}\)-objects with natural real forms.
4. **Reduced comparison.**  Maximal Hausdorff quotient commutes with the
   finite-stage limit and identifies
   \[
   \bar H^\bullet_{\mathcal F}
      (S_{\mathrm{arith}};\mathscr S_{\mathrm{arith}})
   \cong H^\bullet_{\mathrm{arith}}
      (X_W,\mathscr A_{\mathrm{arith}}).                            \tag{2}
   \]
5. **Conformal flow.**  The transverse flow lifts to
   \(S_{\mathrm{arith}}\), maps leaves holomorphically to leaves, and
   scales the reduced Kähler class by
   \[
   (\phi^t)^*[\omega_{\mathcal F}]
   =e^t[\omega_{\mathcal F}].                                      \tag{3}
   \]
6. **Arithmetic orbits.**  Primitive compact orbits are the prime
   packets, have length \(\log p\), and their oriented linearized return
   maps are holomorphic, nondegenerate at every iterate, and agree with
   the MW residue/Gysin orientation.  Then
   `DAC_COMPLEX_LEAF_PRIME_ORBIT_SIGN` gives the positive local
   Lefschetz sign and exact \(\log p\) coefficient.
7. **Archimedean boundary.**  The real signature class is the leafwise
   fundamental orientation and supplies the real form
   \(H^2_{\mathrm{arith},\mathbb R}\cong\mathbb R(-1)\), whose
   complexification is \(H^2_{\mathrm{arith}}\cong\mathbb C(-1)\).
   Its stationary normal
   linearization satisfies
   `DAC_REAL_PLACE_FIXED_POINT_LINEARIZATION`.
8. **Hilbert regularity.**  Leafwise Laplacians are essentially
   self-adjoint on a common core.  At each compact Riemannian stage,
   the positive preserved metric makes coefficient parallel
   translation unitary, so the Benameur--Heitsch theorem makes the
   harmonic projector transversely smooth and identifies its range
   with reduced \(L^2\)-cohomology.  Harmonic projectors are compatible
   across stages, and the centered flow is strongly continuous on the
   harmonic Hilbert completion.
9. **Pro-nuclear trace.**  Test-function-smoothed flow operators are
   nuclear at the limit and finite-stage Lefschetz distributions converge
   in \(\mathcal D'(\mathbb R)\), while reduced \(H^1\) is
   infinite-dimensional.

## Forced consequences

From clauses 1, 4, 5, and 8,
`DAC_KAHLER_RIEMANN_FLOW_PURITY` gives
\[
 \Theta_n=\frac n2+S_n,\qquad S_n^*=-S_n.
\]
Clause 6 supplies the geometric input for a Guillemin--Sternberg/Deninger
distributional Lefschetz formula.  Clauses 2 and 7 transport cup,
trace, and Poincaré duality to the three-term arithmetic complex.

Thus construction of this one object closes the source Hodge positivity
gate; it does not by itself identify the spectrum with zeta zeros.

## Construction program

1. Refine each finite pro-Stein character chart by a one-complex-dimensional
   leaf chart carrying the logarithmic Kummer differential.
2. Glue charts through rational-Witt finite correspondences and twisted MW
   residue maps, with genuinely quaternionic coefficient transitions.
3. Construct a bundle-like metric whose leafwise area form represents the
   Tate orientation and whose Kummer restriction is the adelic
   \(L^2\) energy form, while the accompanying \(L^1\) topology retains
   the product-formula boundary.
4. Prove transition maps are leafwise holomorphic and preserve the metric
   up to the Frobenius scale.
5. Establish `(1)` only after the quotient-adapted hypercover,
   Rost--Schmid localization cone, and real boundary have been
   constructed.  Do not compare a two-real-dimensional leaf complex
   with the raw local two-term coefficient.
6. Prove closed-range/reduced Hodge decomposition stagewise and then the
   limit theorem in clause 4.
7. Identify prime return maps and the archimedean orientation before any
   comparison with the explicit formula.

## Falsifiers

- A leaf model of complex dimension other than one gives the wrong
  arithmetic cohomological dimension.
- Identifying the real leafwise de Rham complex with the raw local
  coefficient before Rost--Schmid/real-boundary totalization is a type
  error and loses or double-counts degree two.
- A metric defined using zeta zeros, Xi, Weil positivity, or RH is
  circular.
- A functorial untwisted real form on degree one for all number fields
  contradicts Deninger's no-real-coefficients theorem.  An extra real
  form on the isolated \(\mathbb Q\) object is not a falsifier.
- If `(3)` has scale \(e^{ct}\) with \(c\ne1\), middle purity is on
  \(\operatorname{Re}s=c/2\), not the critical line.
- If the generic leaf is not dense, top reduced cohomology and
  Poincaré duality need not have the required one-dimensional form.
- Formal Hodge star without closed reduced differentials does not give
  the needed Hilbert-space adjoint theorem.
- A single finite-dimensional harmonic sector is ruled out by
  `DAC_SINGLE_FINITE_TRANSVERSE_LAMINATION_NO_GO`.
- A bare \(L^2\) Kummer realization is ruled out by
  `DAC_NAIVE_ADELIC_L2_KUMMER_COMPLETION_NO_GO`; it loses the
  product-formula constraint and has identity centered power action.

## Current status

- Kähler--Riemann Hodge decomposition, Poincaré duality, polarization,
  and conformal-flow purity: literature/paper-proved in the untwisted
  case.  Twisted reduced \(L^2\)-Hodge decomposition and transverse
  smoothness are literature-proved under the exact
  Benameur--Heitsch hypotheses above.  The positive-unitary twisted
  degree-one conformal-flow purity consequence is paper-proved in
  `DAC_TWISTED_KAHLER_RIEMANN_FLOW_PURITY`.
- Abstract three-term purity implication: paper-proved; Lean written,
  direct check deferred during external build saturation.
- Arithmetic leaf refinement, coefficient pushforward comparison,
  odd coefficient descent, mixed \(L^1/L^2\)
  coefficient pushforward comparison, bundle-like conformal metric,
  and reduced limit theorem: open.  Genuine no-real \(Q_8\)/Steinberg
  descent remains open for the all-number-fields extension, but is not
  on the \(\zeta_{\mathbb Q}\)-to-RH critical path.

**Verdict:** `ACTIVE SOURCE CONJECTURE; EXACT HODGE/POSITIVITY
CONSTRUCTION GATE`.

## Log

- 2026-07-26 — Created after extracting Deninger--Singhof Proposition
  4.6 and separating geometric positivity from zero-defined Hilbert
  targets.
- 2026-07-26 — Corrected the geometric comparison target from the raw
  local coefficient to the full arithmetic localization totalization.
- 2026-07-27 — Replaced the forbidden untwisted real degree-one
  coefficient by a genuinely twisted complex \(K_{\mathbb R}\)-odd
  local system, while retaining real forms only on endpoint lines.
- 2026-07-27 — Audited Benameur--Heitsch's primary source.  Refined the
  coefficient to a positive Hermitian quaternionic local system, which
  makes parallel transport bounded and therefore supplies the finite
  stage reduced \(L^2\)-Hodge decomposition and transversely smooth
  harmonic projector.  Recorded explicitly that their theorem does not
  construct the arithmetic coefficient or Poisson comparison.
- 2026-07-27 — Corrected the scope of Deninger's no-real theorem.
  Genuine no-real descent is required for functoriality over all number
  fields; the \(\mathbb Q\) RH stage requires odd \(K_{\mathbb R}\)
  parity but may carry an additional real form.
