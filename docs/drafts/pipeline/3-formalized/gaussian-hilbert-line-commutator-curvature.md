# Gaussian Hilbert-line commutator curvature law

- **ID:** gaussian-hilbert-line-commutator-curvature
- **Stage:** 3-formalized
- **Type:** FAILURE-DRIVEN SURVIVOR / FRONTIER BASE CASE (Lean)
- **Novelty:** `[NOVELTY CANDIDATE AFTER EXACT-STATEMENT SEARCH]`; not yet a discovery claim
- **Parent card:** `gaussian-hilbert-fano-curvature`

## The law

Let \(x_1,\ldots,x_N\) be distinct points in a real Hilbert space whose affine span has
dimension one, let

\[
  K_X(t)_{ij}=\exp(-t\lVert x_i-x_j\rVert^2),\qquad t>0,
\]

and let \(A_t\) be the compression of the annihilation operator in the unique affine
direction to the span of the coherent vectors
\(\varepsilon(\sqrt{2t}\,x_i)\), after translating the configuration into that line.
Then

\[
 -t^2\frac{d^2}{dt^2}\log\det K_X(t)
   =\frac12\lVert[A_t,A_t^*]\rVert_{\mathrm{HS}}^2.       \tag{HLCC}
\]

In particular,

\[
  \frac{d^2}{dt^2}\log\det K_X(t)<0
\]

for every \(t>0\) whenever \(N>1\).

The identity is independent of the chosen origin and unit vector on the affine line.
Changing the unit vector replaces \(A_t\) by \(-A_t\), leaving the commutator fixed;
translation adds a scalar multiple of the identity to \(A_t\), also leaving the
commutator fixed.

## Dependency-closed proof

### 1. Fock--Pluecker degree law

After a common translation, write the points as \(x_i=\xi_i e\) for a unit vector
\(e\).  Put

\[
 S_t=\operatorname{span}\{\varepsilon(\sqrt{2t}\,\xi_i e):1\le i\le N\}
\]

and let \(P_t\) be its orthogonal projection.  The normalized exterior product of a
basis of \(S_t\) has the same homogeneous-degree law \(D\) as the nonnegative
Fock--Pluecker expansion of

\[
 Z_X(t)=e^{2tE_X}\det K_X(t).
\]

The ordinary partition identities give

\[
 t^2(\log\det K_X)''=\operatorname{Var}_t(D)-\mathbb E_tD. \tag{1}
\]

### 2. Annihilation-compression defect

Let \(a=a(e)\), and let

\[
 A_t=P_taP_t\vert_{S_t}.
\]

Every coherent vector in the displayed spanning family is an eigenvector of \(a\), so
\(S_t\) is invariant under \(a\).  The Slater one-body variance formula, followed by
the canonical commutation relation \([a,a^*]=I\), gives the one-mode specialization
of the annihilation-defect identity:

\[
 \mathbb E_tD-\operatorname{Var}_t(D)
   =\operatorname{tr}((A_t^*A_t)^2)-\lVert A_t^2\rVert_{\mathrm{HS}}^2. \tag{2}
\]

For completeness, if

\[
 a=\begin{pmatrix}A_t&B_t\\0&C_t\end{pmatrix}
 \quad\text{on }S_t\oplus S_t^\perp,
\]

then the upper-left CCR block is

\[
 B_tB_t^*=I+A_t^*A_t-A_tA_t^*.
\]

Moreover \((1-P_t)\mathcal NP_t=B_t^*A_t\), where
\(\mathcal N=a^*a\).  Hence

\[
 \operatorname{Var}_t(D)
 =\lVert B_t^*A_t\rVert_{\mathrm{HS}}^2
 =\operatorname{tr}(A_t^*B_tB_t^*A_t)
 =\mathbb E_tD+\lVert A_t^2\rVert_{\mathrm{HS}}^2
   -\operatorname{tr}((A_t^*A_t)^2),
\]

which is (2).

### 3. Exact self-commutator square

For every finite-dimensional operator \(A\), cyclicity of trace gives

\[
 \begin{aligned}
 \lVert[A,A^*]\rVert_{\mathrm{HS}}^2
 &=\operatorname{tr}\bigl((AA^*-A^*A)^2\bigr)\\
 &=\operatorname{tr}((AA^*)^2)+\operatorname{tr}((A^*A)^2)
   -2\operatorname{tr}(AA^*A^*A)\\
 &=2\operatorname{tr}((A^*A)^2)-2\lVert A^2\rVert_{\mathrm{HS}}^2.
 \end{aligned}
\]

Therefore (2) is exactly

\[
 \mathbb E_tD-\operatorname{Var}_t(D)
   =\frac12\lVert[A_t,A_t^*]\rVert_{\mathrm{HS}}^2.       \tag{3}
\]

Combining (1) and (3) proves (HLCC).

### 4. Strictness

The coherent vectors spanning \(S_t\) are linearly independent because the Gaussian
kernel is strictly positive definite on distinct points.  They are eigenvectors of
\(A_t\) with the distinct real eigenvalues \(\sqrt{2t}\,\xi_i\).

If \([A_t,A_t^*]=0\), then \(A_t\) is normal.  Eigenvectors of a normal operator that
belong to distinct eigenvalues are orthogonal.  But any two exponential vectors have

\[
 \left\langle\varepsilon(\sqrt{2t}\,\xi_i e),
   \varepsilon(\sqrt{2t}\,\xi_j e)\right\rangle
 =\exp(2t\xi_i\xi_j)>0,
\]

so they are never orthogonal.  This contradiction shows
\([A_t,A_t^*]\ne0\) for \(N>1\), and (HLCC) is strictly positive on its right-hand
side.

## Anti-theatre audit

- The finite-matrix self-commutator identity is parent algebra, not new science.
- Coherent-vector Gram formulas, Slater moment formulas, and the CCR are parent theory.
- The candidate scientific content is the exact metric law (HLCC): Gaussian determinant
  curvature on every finite Hilbert-line metric is precisely compressed-annihilator
  non-normality energy, with a rigidity characterization.
- Searches for Gaussian-kernel determinant concavity, coherent Gram determinant curvature,
  Hilbert--Schmidt commutator formulas, and Mandel statistics of coherent Slater states found
  the parent subjects but no statement equivalent to (HLCC).  This is an exact-statement
  search boundary, not proof of global absence.
- The theorem is the maximal unconditional survivor currently available.  It does not imply
  the higher-dimensional coherent row--column compensation conjecture.

## Lean ownership

Formalize in layers:

1. the finite real matrix self-commutator trace identity;
2. the one-mode specialization of the annihilation-defect identity;
3. the connector from the Fock--Pluecker degree law to Gaussian determinant curvature;
4. strictness from distinct eigenvalues and nonorthogonal coherent eigenvectors.

Only layer 1 is parent infrastructure.  The card is not Stage 3 until the full statement
(HLCC), including its connector and strictness, is compiled unconditionally.

`[LEAN-PROVED]` All four layers are compiled.

Layer 1 is `GaloisForLFunctions.HilbertMetric.FanoCommutator`: the exact two-times-defect
identity, nonnegativity, and the equality/normality criterion.

Layers 2--4 are `GaloisForLFunctions.HilbertMetric.HilbertLineCommutatorCurvature`
(imported by `GaloisForLFunctions.HilbertMetric`).  Every theorem builds with no warnings and
`#print axioms` returns exactly `propext, Classical.choice, Quot.sound`.

| Card item | Lean name |
|---|---|
| Gaussian Gram of a line configuration | `hilbertLineGaussianGram`, `hilbertLineGaussianGram_posDef` |
| coherent Gram `⟪ε u, ε v⟫ = exp ⟪u,v⟫` | `hilbertLineCoherentGram`, `hilbertLineCoherentGram_eq_gaussianCoherentGram`, `hilbertLineCoherentGram_posDef` |
| compressed annihilator `A_t` | `hilbertLineAnnihilationCompression` |
| `A_t` is well defined (any square root of the Gram) | `selfCommutator_energy_sqrtSimilarity_eq_of_gram` |
| gauge invariance of the compression | `selfCommutator_energy_sqrtSimilarity_gauge` |
| curvature connector `(1)`–`(3)` | `hilbertLineGaussian_logDet_secondDerivative_eq` |
| **(HLCC)** | `hilbertLineGaussian_logDet_curvature_eq_selfCommutator` |
| strictness for `N > 1` | `hilbertLineGaussian_logDet_secondDerivative_lt_zero`, `hilbertLineAnnihilationEnergy_pos` |
| independence of the unit vector | `hilbertLineAnnihilationCompression_neg`, `hilbertLineAnnihilationEnergy_reflection_invariant` |
| independence of the origin | `hilbertLineCoherentGram_translate`, `hilbertLineAnnihilationEnergy_translation_invariant` |
| packaged law | `hilbertLineCommutatorCurvatureLaw` |

The formalized statement is

```text
-t^2 * (log det K_X)''(t) = (1/2) * ‖[A_t, A_tᵀ]‖_HS^2 ,
A_t = matrixSqrtSimilarity (coherent Gram at t) (diagonal (√(2t) ξ)) .
```

`A_t` is exactly the matrix, in orthonormal coordinates, of the compression of an operator that
acts diagonally with eigenvalues `√(2t) ξ_i` on a family whose Gram is the coherent Gram
`exp (2t ξ_i ξ_j)` — that is, of the annihilation operator on the coherent family.  That this
depends only on the Gram, and not on the chosen orthonormalization, is
`selfCommutator_energy_sqrtSimilarity_eq_of_gram`: for **every** `R` with `Rᵀ R = G`, the
conjugate `R D R⁻¹` has the same self-commutator energy as the canonical positive-square-root
similarity.

### Reuse

The Fock--Pluecker degree law of the paper proof is not re-derived: the connector goes through the
already compiled arbitrary-background curvature identity
`rankOneSchurGaussian_logDet_secondDerivative_eq`
(`GaloisForLFunctions.HilbertMetric.RankOneSchurGaussianConcavity`), applied after splitting the
bandwidth `t = t/2 + t/2` so that the background `K_X(t/2)` is positive definite.  The coherent
Gram is the corpus object `gaussianCoherentGram`, whose positive definiteness criterion
`gaussianCoherentGram_posDef_iff_injective` is reused verbatim, and the positive-definiteness of
the line Gram comes from `finiteGaussianDistanceGram_posDef_of_injective_of_pos`.  Strictness is
`rankOneSchurGaussian_logDet_secondDerivative_lt_zero` with the everywhere-nonzero Gaussian
background and nonconstant labels.

## Log

- 2026-07-19 -- extracted from the failure of the arbitrary-tuple commutator-square shortcut;
  completed the paper proof and isolated affine dimension one as the exact anomaly-free base
  case of the higher-dimensional frontier.
- 2026-07-19 -- compiled the unconditional finite real matrix self-commutator parent layer;
  the coherent Fock connector and strict Hilbert-line theorem are not yet Lean-formalized.
- 2026-07-26 -- compiled layers 2--4: Gram-invariance of the compressed-eigenoperator energy, the
  exact (HLCC) connector, strictness, and the origin/direction invariances.  Card moved to
  `3-formalized`.
