# Metric-phase exactness, cost, winding, and cofinal strictness law

- **ID:** ULF-MPE-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** universal-law-field speculative tournament
- **Statement:** Algebraically identical acyclic laws can have independent conditioning, determinant phase, lifted winding, and cofinal strictness data.

## Goal

Produce one route-independent finite-to-cofinal model coupling five corpus organs without identifying
them: exactness, positive cost, phase loss, recurrent observation with open history, and completion
failure.

## Gates

- [x] 0 → 1: explicit source-free finite family and cofinal system
- [x] 1 → 2: dependency-closed proof below
- [~] 2 → 3: Theorems 1 and 2 Lean-certified in
  `GaloisForLFunctions.HTGeometry.ConstitutiveMetricPhaseExactness`; Theorem 3 (cofinal Hilbert
  direct sum) still open
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

## Lean certification status (2026-08-09)

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveMetricPhaseExactness`
(wired into `HTGeometry.UniversalLawField`).

Certified — Theorem 1: `det_metricPhaseLaw` (the determinant amplitude `e^{iφ} sin α`),
`conjTranspose_mul_self` (`TᴴT = !![1, cos α; cos α, 1]`, phase-blind), `det_gramLaw` (`sin²α`),
`gramLaw_mulVec_low` / `gramLaw_mulVec_high` (Gram eigenvectors `(1,∓1)` with eigenvalues
`1 ∓ cos α`, the squared singular values), `det_metricPhaseLaw_ne_zero` (acyclicity for
`0 < α ≤ π/2`), `gram_phase_erasure` together with `det_phase_separates` (the Gram reading erases
the phase, the determinant does not).

Certified — Theorem 2: `metricPhaseLaw_periodic` (exact `2π`-periodicity of the observed law),
`exp_detLogLift` (the lift really lifts the determinant), `detLogLift_period` (advance `2πi` per
observed period) and `detLogLift_winding` (winding `N` after `N` periods).

Open — Theorem 3: the cofinal Hilbert direct sum `⨁ T_{α_n,0}` on `ℓ²(ℕ;ℂ²)`, its boundedness,
injectivity, dense nonclosed proper range, and the divergence of `‖T_N⁻¹‖²` and of the determinant
free energy. This needs a Hilbert-direct-sum and closed-range layer that the corpus does not yet
carry; the operator-norm form of (4) is likewise deferred to that layer.
