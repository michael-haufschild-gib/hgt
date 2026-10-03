### Parity-Drift Hypothesis for π

Write the binary expansion of π as
\[
\pi = 11.b_1b_2b_3\ldots,\qquad b_n\in\{0,1\}.
\]

We hypothesise that the binary digits of π contain a weak but persistent positional bias that distinguishes odd and even digit positions.

Define the parity-conditioned frequencies
\[
p_{\mathrm{odd}}(N)
=
\frac1N\sum_{n=1}^{N} b_{2n-1},
\qquad
p_{\mathrm{even}}(N)
=
\frac1N\sum_{n=1}^{N} b_{2n}.
\]

The hypothesis is that these two subsequences do not both converge to the unbiased value \(1/2\). In its strongest form, there exists a constant \(\delta\neq0\) such that
\[
p_{\mathrm{odd}}(N)\to \frac12+\delta,
\qquad
p_{\mathrm{even}}(N)\to \frac12-\delta.
\]

Thus the overall proportion of binary \(1\)'s may still converge to \(1/2\), because the two biases cancel, while the expansion retains a persistent period-two statistical structure.

Equivalently, define the parity drift
\[
D(N)
=
\sum_{n=1}^{N}\bigl(b_{2n-1}-b_{2n}\bigr).
\]

The central objective is to prove that
\[
\limsup_{N\to\infty}\frac{|D(N)|}{N}>0,
\]
or, more strongly,
\[
\frac{D(N)}{N}\to 2\delta\neq0.
\]

Such a result would prove that π is not normal in base \(2\). Base-2 normality requires the binary expansion to have no persistent statistical dependence on position modulo \(2\); in particular, the odd- and even-position subsequences must each have asymptotic density \(1/2\) of zeros and ones.

### Research objective

We are therefore looking for an arithmetic mechanism in π that produces a very small but non-vanishing correlation between the value of the \(n\)-th binary digit and the parity of \(n\).

The target is not merely to find finite numerical bias. Nor is it enough to prove an unbounded discrepancy such as
\[
D(N)\to\infty
\]
if \(D(N)=o(N)\).

What must be established is an asymptotically persistent defect: a parity-conditioned frequency, block frequency, or related statistic whose normalised discrepancy fails to vanish as \(N\to\infty\).

The broader hypothesis is therefore:

> The binary expansion of π is globally balanced but contains a weak periodic statistical defect, invisible in the unconditioned one-digit distribution, which survives asymptotically and thereby obstructs base-2 normality.

The programme is to identify this defect analytically, determine its asymptotic size, and prove that it cannot decay sufficiently rapidly to restore normality.