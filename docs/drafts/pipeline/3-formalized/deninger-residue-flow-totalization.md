# Deninger two-term endomorphism-fiber totalization

- **ID:** `deninger-residue-flow-totalization`
- **Stage:** 3-formalized
- **Type:** THEOREM / two-term mapping-fiber prototype
- **Parent:** `deninger-rost-schmid-flow-realization`
- **Novelty:** `[REDISCOVERED]` standard two-direction total-complex algebra

## Statement

Let \(R\) be a commutative ring, let \(A^0,A^1\) be \(R\)-modules, and let
\[
  \partial:A^0\to A^1,\qquad
  \nabla^0:A^0\to A^0,\qquad
  \nabla^1:A^1\to A^1
\]
be \(R\)-linear maps satisfying
\[
  \nabla^1\partial=\partial\nabla^0.                 \tag{1}
\]
Define
\[
\begin{aligned}
  C^0&=A^0,\\
  C^1&=A^1\oplus A^0,\\
  C^2&=A^1,\\
  d^0(a)&=(\partial a,\nabla^0a),\\
  d^1(b,a)&=\nabla^1b-\partial a.
\end{aligned}                                        \tag{2}
\]
Then:

1. \(d^1d^0=0\).
2. Degree-zero cocycles are exactly
   \[
     \ker\partial\cap\ker\nabla^0.
   \]
3. The image of \(d^1\) is
   \[
     \operatorname{im}\nabla^1+\operatorname{im}\partial,
   \]
   so
   \[
     H^2(C^\bullet)
       =A^1/(\operatorname{im}\nabla^1+\operatorname{im}\partial).
   \]
4. Middle cohomology is exactly
   \[
     \frac{\{(b,a)\in A^1\oplus A^0:
       \nabla^1b=\partial a\}}
      {\{(\partial x,\nabla^0x):x\in A^0\}}.
   \]

## Proof

For \(a\in A^0\), equations `(1)` and `(2)` give
\[
  d^1d^0(a)
    =d^1(\partial a,\nabla^0a)
    =\nabla^1\partial a-\partial\nabla^0a
    =0.
\]
This proves item 1.

By `(2)`, \(d^0(a)=0\) if and only if both coordinates vanish, namely
\(\partial a=0\) and \(\nabla^0a=0\).  This is item 2.

Every value of \(d^1\) has the form
\(\nabla^1b-\partial a\), hence belongs to
\(\operatorname{im}\nabla^1+\operatorname{im}\partial\).  Conversely,
if \(y=\nabla^1b+\partial a\), then
\[
  y=d^1(b,-a).
\]
Thus the two submodules are equal.  Taking the cokernel of \(d^1\) proves item 3.

Finally, \(d^1(b,a)=0\) exactly when
\(\nabla^1b=\partial a\), while the degree-one coboundaries are exactly the pairs
\((\partial x,\nabla^0x)\) in the image of \(d^0\).  Item 1 shows that every such pair is a
cocycle, so quotienting gives item 4.

All dependencies are explicit and the proof is complete.

## Correct Deninger interpretation

Take \(A^0\to A^1\) to be any two-term cochain complex and \(\nabla\) to be a commuting
chain endomorphism, such as \(\Theta-n\).  Then `(2)` is its mapping-fiber totalization.
Flach--Morin conjecture that Weil--Arakelov cohomology is precisely
\(\operatorname{Fib}(\Theta-n)\) on Deninger's dynamical complex.

This theorem must **not** be read as constructing Deninger's dynamical \(H^0,H^1,H^2\):
the transverse flow generator acts on the leafwise cochain complex and is not a second
cohomological differential.  A three-term dynamical complex has a four-term mapping fiber;
that exact construction is formalized by `DeningerArithmeticWeilArakelovFiber.lean`.

This theorem does not construct the Rost--Schmid coefficient sheaf, archimedean boundary,
positive Hodge operator, determinant comparison, or RH proof.

## Formalization status

- `[PAPER-PROVED]` Exact theorem above.
- `[LEAN-PROVED]` `DeningerArithmeticResidueFlowTotalization.lean` defines the three
  cochain groups, both differentials, all three cohomology carriers, and proves the
  nilpotence, endpoint, middle-cocycle, middle-coboundary, and top-image formulas.
- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/DeningerArithmeticResidueFlowTotalization.lean`
  exits successfully with no output.
- The source contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Exact `#print axioms` is deferred until the final permitted module build creates the
  importable `.olean`.
