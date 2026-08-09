# Metric-phase exactness, cost, winding, and cofinal strictness law

- **ID:** ULF-MPE-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveMetricPhaseExactness`
- **Source:** universal-law-field speculative tournament
- **Statement:** Algebraically identical acyclic laws can have independent conditioning, determinant phase, lifted winding, and cofinal strictness data.

## Goal

Produce one route-independent finite-to-cofinal model coupling five corpus organs without identifying
them: exactness, positive cost, phase loss, recurrent observation with open history, and completion
failure.

## Gates

- [x] 0 → 1: explicit source-free finite family and cofinal system
- [x] 1 → 2: dependency-closed proof below
- [x] 2 → 3: Theorems 1, 2 and 3 Lean-certified in
  `GaloisForLFunctions.HTGeometry.ConstitutiveMetricPhaseExactness`, on the new reusable layer
  `GaloisForLFunctions.HTGeometry.HilbertBlockOperator`
- [ ] 3 → 4: no publication/priority claim

## 1. Finite exact-law family

Fix (0<\alpha\le \pi/2) and (\phi\in\mathbb R). Define

\[
T_{\alpha,\phi}=\begin{pmatrix}
1&\cos\alpha\\
0&e^{i\phi}\sin\alpha
\end{pmatrix}:\mathbb C^2\longrightarrow\mathbb C^2.
\tag{1}
\]

Regard (0\to\mathbb C^2\xrightarrow{T_{\alpha,\phi}}\mathbb C^2\to0) as a
based Hilbert complex.

## Theorem 1 — exactness has a metric and a phase invisible to the derived endpoint

For every (0<\alpha\le\pi/2):

1. (T_{\alpha,\phi}) is invertible, so the complex is acyclic and isomorphic to zero in the
   derived category.
2. Its determinant amplitude and positive Gram energy are
   \[
   \det T_{\alpha,\phi}=e^{i\phi}\sin\alpha,
   \qquad
   \det(T_{\alpha,\phi}^*T_{\alpha,\phi})=\sin^2\alpha.
   \tag{2}
   \]
3. The singular values are
   \[
   s_{\min}=\sqrt{1-\cos\alpha},
   \qquad
   s_{\max}=\sqrt{1+\cos\alpha}.
   \tag{3}
   \]
   Hence worst unit-target filling energy is
   \[
   \sup_{\|y\|=1}\inf_{Tx=y}\|x\|^2
   =\|T^{-1}\|^2=\frac1{1-\cos\alpha}.
   \tag{4}
   \]
4. Positive Gram data determine (\alpha) but erase (\phi). In particular no
   Gram-invariant rule recovers the phased determinant.

### Proof

The determinant in (2) is nonzero. Direct multiplication gives

\[
T^*T=\begin{pmatrix}1&\cos\alpha\\\cos\alpha&1\end{pmatrix},
\tag{5}
\]

whose eigenvalues are (1\pm\cos\alpha). This proves (2)--(4). Equation (5) is independent
of (\phi), while (2) winds with (\phi), proving phase erasure. ∎

## Theorem 2 — closed observation, open determinant history

Fix (\alpha) and put (T(t)=T_{\alpha,t}). Then

\[
T(t+2\pi)=T(t),\qquad T(t)^*T(t)=T(0)^*T(0),
\tag{6}
\]

but the basepoint lift of the determinant logarithm is

\[
\widetilde{\log\det T}(t)=\log(\sin\alpha)+it.
\tag{7}
\]

Thus each observed law and every positive cost return after (2\pi), while determinant history
advances by (2\pi i). After (N) observed periods its winding is (N).

### Proof

Equations (6)--(7) follow directly from (1)--(2). ∎

## 2. Cofinal exactness wall

Let (\alpha_n\downarrow0), and form the Hilbert direct-sum operator

\[
\mathcal T=\bigoplus_{n\ge1}T_{\alpha_n,0}
:\ell^2(\mathbb N;\mathbb C^2)\longrightarrow
 \ell^2(\mathbb N;\mathbb C^2).
\tag{8}
\]

Every finite truncation (\mathcal T_N) is invertible.

## Theorem 3 — finite exactness does not imply cofinal strictness

The operator (\mathcal T) is bounded and injective with dense, nonclosed proper range. Moreover,

\[
\|\mathcal T_N^{-1}\|^2
=\max_{n\le N}\frac1{1-\cos\alpha_n}\longrightarrow\infty,
\tag{9}
\]

and the finite determinant free energy

\[
F_N=-\log|\det\mathcal T_N|
=-\sum_{n=1}^N\log(\sin\alpha_n)
\longrightarrow\infty.
\tag{10}
\]

### Proof

Equation (3) gives (\|T_{\alpha_n,0}\|\le\sqrt2), so the direct sum is bounded. Every
block is injective, hence so is (\mathcal T). Every block of (\mathcal T^*) is injective,
so (\ker\mathcal T^*=0) and
(\overline{\operatorname{ran}\mathcal T}=(\ker\mathcal T^*)^\perp) is the whole target.

Choose a unit right-singular vector (x_n) for the least singular value in block (n). Then

\[
\|\mathcal T x_n\|=\sqrt{1-\cos\alpha_n}\longrightarrow0.
\]

A bounded injective operator with closed range is bounded below, so the range is not closed and
therefore is proper. Equations (9)--(10) follow from (2)--(4); since
(\sin\alpha_n\to0), the summands in (10) tend to (+\infty). ∎

## 3. Exact conclusions

This single family proves the logical independence of four decategorifications:

| layer | invariant | what can be lost |
|---|---|---|
| algebraic endpoint | acyclicity / derived zero | all metric and phase data |
| positive law | (T^*T), filling energy | determinant phase and winding |
| exact history | (\det T\in\mathbb C^\times) | higher nonabelian filling data |
| cofinal realization | closed range / uniform inverse | not determined by finite exactness |

In particular:

- derived or homological equivalence cannot reconstruct quantitative proof cost;
- positivity is an exact phase quotient in this family, but not a universal theorem about every
  positive observer;
- recurrent observed law does not imply closed lifted history;
- every finite aperture can be exact while the cofinal Hilbert law is non-strict.

## 4. Hostile scope

All ingredients are classical finite Hilbert-complex, determinant, and closed-range mathematics.
The result is a route-independent calibration and a constraint on any new field, not a novelty claim.
It does not derive (\alpha_n), choose a source amplitude, imply hypertranscendence, or prove any RH
statement. A universal field must retain this four-layer separation rather than rename all layers
"curvature."

## Log

- 2026-08-09 — dependency-closed paper theorem created; no Lean, no route specialization.

## Lean certification status (2026-08-09) — COMPLETE

Modules: `GaloisForLFunctions.HTGeometry.ConstitutiveMetricPhaseExactness` and the new reusable
layer `GaloisForLFunctions.HTGeometry.HilbertBlockOperator` (both wired into
`HTGeometry.UniversalLawField`).

Theorem 1: `det_metricPhaseLaw`, `conjTranspose_mul_self`, `det_gramLaw`, `gramLaw_mulVec_low`,
`gramLaw_mulVec_high`, `det_metricPhaseLaw_ne_zero`, `gram_phase_erasure`, `det_phase_separates`;
the filling energy (4) is `apertureBlock_filling_energy` (upper bound with attainment).

Theorem 2: `metricPhaseLaw_periodic`, `exp_detLogLift`, `detLogLift_period`, `detLogLift_winding`.

Theorem 3: `cofinal_exactness_wall` — the Hilbert direct sum `cofinalLaw` of the aperture blocks is
bounded by `√2`, injective, has dense range, is not surjective, its range is not closed, and both
`(1 − cos α_n)⁻¹` and the determinant free energy `−∑ log sin α_n` diverge.

Supporting metric layer: `euclid2_norm_sq`, `apertureBlock_apply_zero/one`,
`apertureBlock_norm_sq`, `apertureBlock_norm_sq_le`, `norm_apertureBlock_le`,
`apertureBlock_norm_sq_ge`, `one_sub_cos_pos`, `apertureBlock_injective`,
`apertureBlock_surjective`, `lowVector`/`lowUnit` and their norms.

New corpus infrastructure: `HilbertBlockOperator` supplies the operator-valued block diagonal on a
Hilbert direct sum — `blockOperator_memℓp`, `blockOperator`, `norm_blockOperator_le`,
`blockOperator_injective`, `blockOperator_single`, `denseRange_blockOperator`,
`not_surjective_blockOperator`, `range_blockOperator_ne_top`,
`not_isClosed_range_blockOperator` — generalizing the corpus's scalar block diagonal to arbitrary
uniformly bounded blocks.

`#print axioms` on every capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.
