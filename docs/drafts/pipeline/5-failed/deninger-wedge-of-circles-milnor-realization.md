# Wedge-of-circles Milnor realization

- **ID:** `deninger-wedge-of-circles-milnor-realization`
- **Stage:** 5-failed
- **Type:** FAILED LOCAL REALIZATION
- **Parent:** `deninger-relative-sullivan-milnor-character-space`
- **Positive survivor:** `DAC_RELATIVE_MILNOR_CHARACTER_REALIZATION`

## Proposed shortcut

For a finite-dimensional real subspace \(V_0\subset V_F\), a wedge of
\(\dim V_0\) circles has real cohomology algebra
\[
 H^\ast\!\left(\bigvee_{v\in\mathcal B}S^1;\mathbb R\right)
 \cong \mathbb R\oplus V_0[-1],
\]
with every product of positive-degree classes zero.  Filtered unions suggest
a space with the same real algebra as
\(K_\ast^M(F)\otimes\mathbb R=\mathbb R\oplus V_F[-1]\).

## Failure

This construction repairs cohomology by replacing the finite-cover theory.
Already for \(\dim V_0\ge2\), the wedge has free fundamental group
\[
 \pi_1\!\left(\bigvee_{\mathcal B}S^1\right)=F_{\mathcal B},
\]
whereas the corresponding torus/character shape has abelian fundamental
group in the finite-dimensional model.  Their finite quotients differ:
\(F_{\mathcal B}\) has nonabelian finite quotients, while an abelian
fundamental group does not.  Passing to filtered or inverse limits does not
remove the finite-stage nonabelian quotients.

Thus the correct cohomology algebra alone does not solve
Kucharczyk--Scholze's requirement
\[
 \operatorname{FEC}(X_F^M)\simeq\operatorname{FEC}(X_F)
\]
or retain profinite fundamental group \(G_F\).

## Positive survivor

The cohomology correction must occur **relative to** \(X_F\), with a fiber
invisible to finite quotients.  `DAC_RELATIVE_SULLIVAN_MILNOR_RESOLUTION`
constructs the required relative algebra:
\[
 C^\ast(X_F;\mathbb R)\longrightarrow Q_F
 \xrightarrow{\sim}\mathbb R\oplus V_F.
\]
Ordinary Sullivan realization of this algebra also fails.  The surviving
topological packet is instead
`DAC_BAUMSLAG_FREE_RATIONAL_MILNOR_PACKET`: Baumslag's free rational group
has the wedge's rational homology, while its kernel over the rational
abelianization is uniquely divisible.  Such a fiber has no nontrivial
finite quotient.

The survivor is still conjectural geometrically.  One must prove
basis-independent coherent packet assembly, twisted Eilenberg--Moore and
effective pro-cover descent, and integral/profinite enhancement.

## No-go closure

- **Negative theorem:** a wedge-of-circles replacement with at least two
  generators does not preserve finite-cover categories.
- **Sharp boundary:** one generator has no degree-two cup product to kill;
  the obstruction starts exactly when two independent unit classes exist.
- **Positive replacement:** a relative realization with finite-quotient-
  invisible fiber, recorded in
  `deninger-relative-sullivan-milnor-character-space`.
- **Lean status:** no Lean formalization requested yet; this elementary
  group-theoretic no-go is not on the current arithmetic-complex critical
  path.

**Verdict:** `FAILED; POSITIVE SURVIVOR EXTRACTED`.
