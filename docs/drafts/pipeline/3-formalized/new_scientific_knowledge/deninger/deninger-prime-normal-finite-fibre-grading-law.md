# Deninger prime-normal finite-fibre grading law

- **ID:** `deninger-prime-normal-finite-fibre-grading-law`
- **Stage:** 3 — formalised in Lean 4
- **Type:** SHARP TOPOLOGY CLASSIFICATION / ROUTE-L ARCHITECTURE THEOREM
- **Parent:** `deninger-affine-gauge-first-suspension-descent`
- **Inputs:** source-horizon maximal verticality; prime-normal Hilbert cyclicity
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC CANDIDATE NEW]`

## Frontier question

The complete prime-normal reader becomes maximally vertical both in the canonical product
topology and in the ordinary Hilbert topology. Merely replacing an operator by a relation or
replacing \(\mathbb C^{\mathbb N}\) by \(\ell^2\) therefore preserves no usable output constraint.

The source-horizon paper leaves a graded completion open. This card determines exactly how fine
that grading must be.

Let

\[
H=\ell^2(\mathbb N,\mathbb C),\qquad
P_j=(p_i^{-j})_{i\ge0}\quad(j\ge1).
\]

Let \(g:\mathbb N_{\ge1}\to G\) assign a grade to every canonical horizon sample. For each
\(\gamma\in G\), put

\[
J_\gamma=\{j\ge1:g(j)=\gamma\}.
\]

The graded reader places \(P_j\) in the \(\gamma=g(j)\) component of

\[
Y_G=\prod_{\gamma\in G}H.
\]

## Conjecture audit

### FG-1 — suspension parity or first-mode degree is enough

False. These give finitely many grades, hence one grade contains infinitely many samples. That
grade saturates all of \(H\).

### FG-2 — any countable grading avoids saturation

False. Countability is irrelevant. Every individual infinite fibre \(J_\gamma\) is already
Hilbert-cyclic.

### FG-3 — finite-fibre grading is the exact boundary

True. Infinite fibres force complete vertical saturation in that grade. Finite fibres produce
only finite-dimensional vertical spans in every grade and therefore avoid maximality.

## Theorem 1 — arbitrary infinite exponent subsequences remain cyclic

For every infinite \(J\subseteq\mathbb N_{\ge1}\),

\[
\overline{\operatorname{span}_{\mathbb C}\{P_j:j\in J\}}=H.       \tag{1}
\]

More generally, for every \(y\in H\),

\[
\overline{\operatorname{span}_{\mathbb C}\{P_j-y:j\in J\}}=H.     \tag{2}
\]

### Proof

Let \(z\in H\) be orthogonal to every \(P_j\), \(j\in J\), and suppose \(z\ne0\). Let \(k\) be the
least index with \(z_k\ne0\), and write \(x_i=p_i^{-1}\). For every \(j\in J\),

\[
0=\overline{z_k}x_k^j+\sum_{i>k}\overline{z_i}x_i^j.
\]

After division by \(x_k^j\),

\[
0=\overline{z_k}+
\sum_{i>k}\overline{z_i}(x_i/x_k)^j.                              \tag{3}
\]

Because \(J\) is infinite it is unbounded. Put \(r_k=x_{k+1}/x_k<1\). Cauchy--Schwarz gives

\[
\left|\sum_{i>k}\overline{z_i}(x_i/x_k)^j\right|
\le
\|z_{>k}\|_2
\left(\sum_{i>k}(x_i/x_k)^2\right)^{1/2}
r_k^{j-1}.                                                       \tag{4}
\]

The middle factor is finite because \(\sum_i p_i^{-2}<\infty\). Letting \(j\to\infty\) through
\(J\) in `(3)` forces \(z_k=0\), contradiction. This proves `(1)`.

For `(2)`, if \(z\) annihilates every \(P_j-y\), then
\(\langle P_j,z\rangle=\langle y,z\rangle\) on \(J\). Since \(P_j\to0\) in \(H\) along every
unbounded \(J\), the common value is zero. Equation `(1)` then gives \(z=0\).

## Theorem 2 — exact grade-saturation law

Let \(X\) be a complex topological vector space and

\[
\mathcal R\subseteq X\times Y_G
\]

a closed complex linear relation. Choose a proposed horizon value \(y_\gamma\in H\) in every
grade. Suppose that for every \(j\ge1\) there are source representatives \(u_{K,j}\to0\) with

\[
\bigl(u_{K,j},\iota_{g(j)}(P_j-y_{g(j)})\bigr)\in\mathcal R.       \tag{5}
\]

If \(J_\gamma\) is infinite, then the \(\gamma\)-coordinate projection of the multivalued fibre
is all of \(H\):

\[
\operatorname{pr}_\gamma(\operatorname{mul}\mathcal R)=H.         \tag{6}
\]

If every fibre of \(g\) is infinite, then

\[
\operatorname{mul}\mathcal R=Y_G,\qquad
\mathcal R=\operatorname{dom}\mathcal R\times Y_G.                \tag{7}
\]

### Proof

Closedness and `(5)` put every
\(\iota_\gamma(P_j-y_\gamma)\), \(j\in J_\gamma\), in the vertical fibre. Define the supported
slice
\[
W_\gamma=\{v\in H:\iota_\gamma(v)\in\operatorname{mul}\mathcal R\}.
\]
This is a closed subspace of \(H\), as the inverse image of the closed vertical fibre under the
continuous coordinate injection. Theorem 1 makes its contained span dense, hence
\(W_\gamma=H\), proving `(6)` in the stronger supported form.

If every grade fibre is infinite, every coordinate projection of the vertical fibre is
surjective. This alone does not imply `(7)` for an arbitrary correlated subspace of a product.
But the vertical fibre contains the independently supported dense family in each grade. Finite
sums approximate every finite grade block, and product-topology closure then gives every element
of \(Y_G\). Domain factorisation follows by vertical translation.

## Theorem 3 — finite-fibre grading is sufficient to avoid forced saturation

Assume every \(J_\gamma\) is finite and put

\[
V_\gamma=
\operatorname{span}_{\mathbb C}
\{P_j-y_\gamma:j\in J_\gamma\},\qquad
V_G=\prod_{\gamma\in G}V_\gamma.                                 \tag{8}
\]

Every \(V_\gamma\) is finite-dimensional and closed. Since \(H\) is infinite-dimensional,
\(V_\gamma\ne H\). Thus \(V_G\) is a proper closed graded vertical carrier containing every
retained reader displacement.

Consequently:

\[
\boxed{\text{a grading avoids forced full Hilbert saturation in every grade}
\iff \text{all grade fibres are finite}.}                         \tag{9}
\]

The backward implication asserts existence of a nonmaximal closed carrier, not construction of
the arithmetic relevant complex.

## Route-L consequence

The first-suspension degree alone is not the missing grade: every canonical horizon sample lands
in degree one, so that grade is infinite-fibred and Hilbert-saturates. Nor can any finite
Postnikov, parity, or two-collar grading solve the problem.

A viable Route-L attachment must retain an unbounded sample/source grade with finite fibres before
closure. Rational-Witt refinement may coexist with this grade, but cannot replace it: refinement
identifies presentations of one packet coefficient, whereas the horizon sample index records
different prime-normal powers.

The next complex must therefore have at least a bigrading

\[
(\text{cohomological/suspension degree},\ \text{source-horizon sample grade})
\]

with a differential that shifts or preserves the second coordinate in a locally finite way.
Forgetting that second grade before taking closed middle boundaries recreates maximal verticality.

## Anti-theatre audit

- This is not “use a grading” as prose. Equation `(9)` is an exact necessary-and-sufficient
  finiteness criterion.
- It invalidates the tempting claim that the already-constructed first suspension supplies enough
  grading.
- It uses the actual prime-normal packets extracted from the positive complete Riemann source.
- It does not claim the product carrier `(8)` is the arithmetic relevant complex; it only proves
  the sharp topological escape boundary.
- Classical cyclicity of a compact simple-spectrum diagonal operator receives no novelty credit.
  Candidate novelty is its source-specific finite-fibre classification and the forced bigrading
  for Route L.

## Lean formalisation

Formal module:

`formal/GaloisForLFunctions/RHTower/CompleteResolutionPrimeNormalFiniteFibreGrading.lean`

The module proves, unconditionally:

1. `completeResolutionPrimeHilbertPacketSpanOn_closure_eq_top`;
2. `completeResolutionPrimeHilbertAffinePacketSpanOn_closure_eq_top`;
3. `completeResolutionPrimeHilbertAffinePacketSpanOn_closure_eq_top_iff`;
4. `closedLinearRelation_completeResolutionPrimeHilbert_fullSupportedSlice`;
5. `closedLinearRelation_completeResolutionPrimeHilbert_fullGradedVertical`;
6. `closedLinearRelation_completeResolutionPrimeHilbert_graded_eq_domain_prod`;
7. `completeResolutionPrimeHilbertFiniteFibreCarrier_isClosed`;
8. `completeResolutionPrimeHilbertFiniteFibreCarrier_isGradewiseProper`;
9. `completeResolutionPrimeHilbert_exists_closed_gradewiseProperCarrier_iff`.

The final theorem is the exact formal version of `(9)`: a closed carrier retaining every
source-defined affine packet and remaining proper in every independently supported grade exists
if and only if every grade fibre is finite.

Verification:

- direct check:
  `lake env lean GaloisForLFunctions/RHTower/CompleteResolutionPrimeNormalFiniteFibreGrading.lean`;
- targeted build:
  `lake build GaloisForLFunctions.RHTower.CompleteResolutionPrimeNormalFiniteFibreGrading`;
- formal lint: clean;
- axiom audit for all capstones: only `propext`, `Classical.choice`, and `Quot.sound`;
- umbrella:
  `formal/GaloisForLFunctions/RHTower.lean`.

No RH hypothesis, zero hypothesis, numerical computation, `sorry`, `admit`, project `axiom`,
`opaque`, or `unsafe` declaration is used.
