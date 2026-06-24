
## 1. Hard-edge conditioning phase diagram for synthetic measures

Use only toy measures:

[
x_n=n^{-\alpha},\qquad w_n=n^{-\beta},
\qquad
\mu_{\alpha,\beta,N}=\sum_{n=1}^{N}w_n\delta_{x_n}.
]

Compute Hankel matrices

[
H^{(\alpha,\beta)}*{ij}=\sum*{n=1}^{N}w_nx_n^{i+j}.
]

Sweep:

[
\alpha\in[0.5,4],\qquad
\beta\in[0,6],\qquad
d=2,\dots,80.
]

Measure:

[
\kappa(H_d),\quad \lambda_{\min}(H_d),\quad
\text{Cholesky pivot decay},\quad
\text{orthogonal-polynomial root drift}.
]
---

## 2. False-negative map for positive Hankel matrices

Construct positive moment matrices from known positive measures, then ask when numerical algorithms falsely report negative eigenvalues.

Use:

[
\mu=\sum_{n=1}^{N} n^{-\beta}\delta_{n^{-\alpha}},
]

and continuous models:

[
d\mu(x)=x^\lambda|\log x|^\theta dx,\qquad x\in(0,1].
]

For each (d), compute sign decisions with:

[
\text{eigh},\quad \text{LDL}^T,\quad \text{Cholesky},\quad \text{QR},\quad \text{interval arithmetic}.
]

Record the first false negative as a function of:

[
d,\quad \text{dps},\quad \alpha,\beta,\lambda,\theta.
]


---

## 3. Basis-sensitivity benchmark

For the same toy positive measures, represent the moment form in several bases:

[
1,x,x^2,\dots,
]

shifted monomials,

[
(x-a)^n,
]

Chebyshev basis on ([0,1]),

orthonormal polynomials computed from Gram–Schmidt,

and barycentric/Lagrange bases at prescribed nodes.

Measure:

[
\kappa,\quad \lambda_{\min},\quad \text{pivot signs},\quad
\text{root locations},\quad
\text{basis transform condition}.
]


---

## 4. Pick-kernel detection resolution for toy signed measures

Take synthetic signed measures:

[
\sigma=\sum_{j=1}^{M}w_j\delta_{x_j}-\varepsilon\delta_a,
]

with known one negative atom. Build the Cauchy transform:

[
m_\sigma(z)=\int\frac{d\sigma(t)}{t-z}.
]

Sample Pick matrices:

[
P_{ij}=\frac{m_\sigma(z_i)-\overline{m_\sigma(z_j)}}{z_i-\overline{z_j}}.
]

Vary:

[
\varepsilon,\quad a,\quad \Im z_i,\quad N_{\text{samples}},\quad \text{noise level}.
]

Measure the probability that the Pick test detects the negative square.

---

## 5. Uvarov threshold failure map

Start with a toy positive measure (\mu), pick exterior or interior point (a), and form

[
\mu_\theta=\mu-\theta\delta_a.
]

The exact finite threshold is

[
\theta_c(d)=\frac1{K_{\mu,d}(a,a)}.
]

Compute how accurately numerical methods recover the sign of

[
H_d(\mu_\theta)
]

as (\theta) approaches (\theta_c(d)).

Sweep:

[
\theta/\theta_c(d)=1\pm 10^{-r},
\qquad r=1,\dots,200.
]

Compare eigenvalue methods, determinant ratios, Schur complements, and interval arithmetic.

---

## 6. Padé false-pole benchmark

Generate moment sequences from known objects:

1. finite atomic measure;
2. infinite atomic measure with known poles;
3. absolutely continuous measure with branch cut;
4. noisy moments from each of the above.

Build generating functions

[
F(z)=\sum_{n=0}^{M}m_nz^n
]

and compute Padé approximants. Measure:

[
\text{true-pole recovery},\quad
\text{false pole/zero pairs},\quad
\text{pole clustering},\quad
\text{sensitivity to moment noise}.
]

---

## 7. Regulator finite-part stress test on toy singular distributions

Choose toy singular functions, not (\xi):

[
f_k(t)=t^{-2k}\phi(t),
]

paired against known smooth distributions

[
W(t)=1+t^2,\qquad W(t)=e^{-t^2},\qquad W(t)=\cos t.
]

Regularize with different cutoffs:

[
\eta(t/\epsilon)\psi(t/R),
]

Gaussian cutoffs,

Mellin cutoffs,

compact bump cutoffs.

Subtract divergent powers and extract the finite part.

Measure whether finite constants agree across regulators and how agreement depends on parity, cutoff smoothness, and order of limits.

---

## 8. Order-of-limits pathology benchmark

For the same toy finite-part setup, compare:

[
\lim_{\epsilon\to0}\lim_{R\to\infty}
]

versus

[
\lim_{R\to\infty}\lim_{\epsilon\to0}.
]

Also test coupled limits:

[
R=\epsilon^{-a}.
]

Measure when the finite part is stable and when it depends on the path.

---

## 9. Random congruence invariance stress test

Generate random symmetric matrices (A) with prescribed inertia, random invertible transforms (C), and compare sign diagnostics for:

[
A,\qquad C^TAC.
]

Use deliberately ill-conditioned (C). Track which algorithms preserve inertia numerically:

[
\text{eigh},\quad LDL^T,\quad QR,\quad SVD-based reduction,\quad interval methods.
]

---

## 10. Negative-square sampling in rational functions with hidden cancellations

Construct rational generalized Nevanlinna functions with known negative-square count but heavy pole-zero cancellations:

[
m(z)=\sum_{j=1}^{N}\frac{w_j}{x_j-z},
]

where positive and negative weights nearly cancel in several regions.

Run Pick-kernel tests with random and structured sample points.

Measure when the correct negative-square count is missed.

---

## 11. Moment non-uniqueness visualizer

Construct truncated moment sequences that admit many representing measures. Use semidefinite programming or Gaussian quadrature reconstruction to find different measures with the same first (2d+1) moments but different support geometry.

Measure how support can move while moments remain fixed.

---

## 12. “Same diagnostics, different truth” toy battery

Build pairs of toy systems where common diagnostics match but the underlying sign/inertia differs.

Example:

[
\mu_1=\sum w_n\delta_{x_n},
]

positive, and

[
\mu_2=\mu_1-\varepsilon\delta_a+\text{small compensating positive atoms},
]

chosen to match the first few moments or condition numbers.

Then compare:

[
\kappa,\quad \lambda_{\min},\quad \text{Christoffel growth},\quad
\text{Padé poles},\quad
\text{Pick samples}.
]

---

## 13. Universal hard-edge profile search on toy measures

Take toy hard-edge measures with different densities:

[
x_n=n^{-\alpha},\quad w_n=n^{-\beta},
]

or continuous:

[
d\mu=x^\lambda|\log x|^\theta dx.
]

Apply a rank-one deletion at a fixed exterior point and study the rescaled local kernel dip.

Ask whether the normalized profile converges to a universal polynomial, Gaussian, Airy/Bessel-like form, or no stable shape.

---

## 14. Determinant-ratio stability benchmark

For generic rank-one updates,

[
A_0=A_-+avv^T,
]

compare numerical computation of

[
a+\frac1{v^TA_-^{-1}v}
]

via:

[
\text{direct inverse},
\quad
\text{linear solve},
\quad
\text{Schur complement},
\quad
-\frac{\det A_0}{\det B},
\quad
\text{log-det}.
]

Sweep condition numbers and dimensions.

---

## 15. Reproducibility fuzzing

Take any toy computation above and run it under:

different precisions,

different BLAS/LAPACK backends if available,

different summation orders,

randomized basis permutations,

different arbitrary-precision libraries,

different quadrature methods.

Measure result drift and produce a reproducibility score.

Why unknown: implementation-level drift is empirical.

No RH usefulness: infrastructure only.

---

## Computations I would **not** run in this quarantine track

These are excluded because they would become useful to the original question:

[
\text{zeta-zero }Q_0\text{ tests},
]

[
s_d\text{ computation},
]

[
\text{Davenport–Heilbronn scalar-gap tests},
]

[
\text{completed explicit-formula source computation},
]

[
\text{Connes–Consani / semilocal prolate matrix comparison},
]

[
\text{anything involving }\xi,\ \zeta,\ \gamma_n,\ \text{or prime explicit-formula transfer}.
]

---

