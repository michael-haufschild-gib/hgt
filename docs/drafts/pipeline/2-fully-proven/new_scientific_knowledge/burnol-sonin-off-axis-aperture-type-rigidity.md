# Burnol--Sonin off-axis aperture-type rigidity

- **ID:** `burnol-sonin-off-axis-aperture-type-rigidity`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / HOSTILE ROUTE AUDIT
- **Scientific status:** `[CORPUS-NEW SYNTHESIS] [PRELIMINARY EXTERNAL NONCOLLISION] [NOT RH]`
- **Parents:**
  - `gamma-copoisson-sonin-independent-quadrant-boundary-transgression.md`;
  - `../not_new_scientific_knowledge/burnol-copoisson-quotient-bilateral-order-rh-law.md`;
  - Burnol's continuous completed-Mellin evaluation theorem for the extended Sonine spaces.
- **Statement:** Away from the critical line, the completed-Mellin evaluation vector in
  Burnol's extended Sonine space has exactly the aperture exponent
  \(\lvert\operatorname{Re}w-\tfrac12\rvert\) on every co-Poisson annihilator fibre.  Hence the
  independent-quadrant section has the exact exponential face growth already predicted by its
  prime-transfer character.  The proposed subexponential estimate `(GS24)` is not generic Sonine
  regularity and cannot be obtained by sharpening an ambient evaluation estimate.

## Set-up

Let \(L_a\subset L^2(0,\infty;dt)\) be Burnol's extended cosine-Sonine space: \(f\) and its
unitary cosine transform \({\cal F}_+f\) are constant on \((0,a)\).  For \(w\notin\{0,1\}\), let
\[
 {\cal M}f(w)
 =\gamma(w)\int_0^\infty f(t)t^{-w}\,dt,
 \qquad
 \gamma(w)=\pi^{-w/2}\Gamma(w/2),
 \tag{1}
\]
denote the completed right Mellin evaluation, meromorphically interpreted where necessary.
Write \(k_{w,a}\in L_a\) for its Riesz vector.

Fix \(a_0>0\), \(r>1\), and
\[
 a_N=a_0r^{-N},\qquad
 \lambda_r(w)=r^{w-1/2}.
 \tag{2}
\]

## Ambient off-axis upper bound

`[PAPER-PROVED] [EXTENDED_SONIN_EVALUATION_APERTURE_UPPER_BOUND]`

If \(0<\sigma=\operatorname{Re}w<1\) and \(\sigma\ne\tfrac12\), then
\[
 \boxed{\quad
 \|k_{w,a}\|
 \le C(w)\,a^{-|\sigma-1/2|}
 \quad}
 \tag{3}
\]
for every \(a>0\), where one may take
\[
\begin{aligned}
C_+(w)
 &=|\gamma(w)|
   \left({1\over|1-w|}+{1\over\sqrt{2\sigma-1}}\right),
 &&\sigma>\tfrac12,\\
C_-(w)
 &=|\gamma(1-w)|
   \left({1\over|w|}+{1\over\sqrt{1-2\sigma}}\right),
 &&\sigma<\tfrac12.
\end{aligned}
\tag{4}
\]

### Proof

Suppose first that \(\sigma>\tfrac12\).  For \(f\in L_a\), write \(f(t)=c\) on \((0,a)\).
Then
\[
 |c|\sqrt a\le\|f\|_2
 \tag{5}
\]
and
\[
 \left|\int_0^a c\,t^{-w}\,dt\right|
 ={ |c|a^{1-\sigma}\over|1-w|}
 \le {a^{1/2-\sigma}\over|1-w|}\|f\|_2.
 \tag{6}
\]
Cauchy--Schwarz on the tail gives
\[
\begin{aligned}
\left|\int_a^\infty f(t)t^{-w}\,dt\right|
&\le\|f\|_2
 \left(\int_a^\infty t^{-2\sigma}\,dt\right)^{1/2}\\
&={a^{1/2-\sigma}\over\sqrt{2\sigma-1}}\|f\|_2.
\end{aligned}
\tag{7}
\]
Multiplication by \(|\gamma(w)|\) proves `(3)` with \(C_+(w)\).

If \(\sigma<\tfrac12\), Burnol's completed Mellin--cosine functional equation gives
\[
 {\cal M}f(w)={\cal M}({\cal F}_+f)(1-w).
 \tag{8}
\]
The cosine transform is unitary, belongs again to \(L_a\), and
\(\operatorname{Re}(1-w)>\tfrac12\).  Apply the already-proved estimate at \(1-w\).  Its aperture
factor is
\[
 a^{1/2-\operatorname{Re}(1-w)}
 =a^{\sigma-1/2},
 \tag{9}
\]
which proves `(3)` with \(C_-(w)\).  `QED`

No estimate is asserted at \(\sigma=\tfrac12\): the tail weight \(t^{-1/2}\) is exactly outside
\(L^2(a,\infty)\), and continuity there uses the full Sonine condition rather than this elementary
split.

## Sharp aperture type on an annihilator fibre

Let \(\rho\) be a nontrivial zeta zero.  Burnol's orthogonal-complement theorem identifies its
co-Poisson quotient vector with the full evaluator:
\[
 y_{\rho,N}=k_{\rho,a_N}\ne0.
 \tag{10}
\]
The two projected dilation maps in the parent boundary-transgression theorem are contractions and
obey the exact characters \(\overline{\lambda_r(\rho)}\) and
\(\overline{\lambda_r(\rho)^{-1}}\).  Consequently,
\[
 \|k_{\rho,a_N}\|
 \ge
 \max\{|\lambda_r(\rho)|^N,|\lambda_r(\rho)|^{-N}\}
 \|k_{\rho,a_0}\|.
 \tag{11}
\]

`[PAPER-PROVED] [ANNIHILATOR_EVALUATION_EXACT_APERTURE_TYPE]`

If \(\operatorname{Re}\rho\ne\tfrac12\), there are constants
\(0<c_\rho\le C_\rho<\infty\), independent of \(N\), such that
\[
 \boxed{\quad
 c_\rho r^{N|\operatorname{Re}\rho-1/2|}
 \le
 \|k_{\rho,a_N}\|
 \le
 C_\rho r^{N|\operatorname{Re}\rho-1/2|}.
 \quad}
 \tag{12}
\]
In particular,
\[
 \boxed{\quad
 \lim_{N\to\infty}{1\over N\log r}
 \log\|k_{\rho,a_N}\|
 =
 |\operatorname{Re}\rho-\tfrac12|.
 \quad}
 \tag{13}
\]

### Proof

The lower bound is `(11)`.  The upper bound follows from `(3)` and
\[
 a_N^{-|\operatorname{Re}\rho-1/2|}
 =
 a_0^{-|\operatorname{Re}\rho-1/2|}
 r^{N|\operatorname{Re}\rho-1/2|}.
 \tag{14}
\]
Taking logarithms and dividing by \(N\log r\) proves `(13)`.  `QED`

Thus horizontal zero displacement is literally the anomalous aperture dimension of the
Gamma-completed Sonine evaluator.  The local Xi residue, prime-shell Lyapunov exponent, and Sonine
norm exponent are the same charge, up to sign and multiplicity.

## Exact independent-face growth

For the parent quadrant section
\[
 X_{p,q}(\rho)
 =\overline{\lambda_r(\rho)}^{\,q-p}
   k_{\rho,a_{p+q}},
 \tag{15}
\]
equation `(12)` sharpens the earlier lower bound to a two-sided law.

If \(\operatorname{Re}\rho>\tfrac12\), then
\[
 c_\rho|\lambda_r(\rho)|^{2q}
 \le\|X_{p,q}(\rho)\|
 \le C_\rho|\lambda_r(\rho)|^{2q}.
 \tag{16}
\]
If \(\operatorname{Re}\rho<\tfrac12\), then
\[
 c_\rho|\lambda_r(\rho)|^{-2p}
 \le\|X_{p,q}(\rho)\|
 \le C_\rho|\lambda_r(\rho)|^{-2p}.
 \tag{17}
\]
These follow immediately by multiplying `(12)` by
\(|\lambda_r(\rho)|^{q-p}\) and using \(N=p+q\).

## Hostile consequence for `(GS24)`

Every off-line annihilator character violates `(GS24)` with its exact source character rate:

- a right-half zero escapes only through the \(q\)-face, with exponent
  \(2(\operatorname{Re}\rho-\tfrac12)\log r\);
- a left-half zero escapes only through the \(p\)-face, with exponent
  \(2(\tfrac12-\operatorname{Re}\rho)\log r\).

Therefore `(GS24)` is not an ambient Sonine estimate waiting for a finer Cauchy--Schwarz
argument.  The ambient estimate is already sharp on every off-axis annihilator fibre.  Proving
`(GS24)` from the arithmetic source would have to prove a new protection or anomaly-cancellation
law which eliminates the off-axis fibres themselves.

Moreover `(GS24)` may be stronger than RH: the theorem says nothing about subexponential growth
of critical-line evaluation norms.  The logically minimal RH reader is the vanishing of the
off-axis aperture exponent `(13)`, not a raw subexponential bound on every critical evaluator.

This closes the strategy

```text
improve ordinary Sonine evaluation estimates
  -> prove subexponential quadrant growth
  -> RH.
```

The surviving problem is not an estimate internal to one evaluator fibre.  It is construction of
a source comparison which forces Xi conormal fibres to be protected, trace-like, or otherwise
zero-anomaly before their individual characters are read.

## Literature boundary

Burnol proves:

1. \(L_a\) consists of functions, and cosine transforms, constant on \((0,a)\);
2. completed Mellin evaluations are continuous;
3. the co-Poisson orthogonal complement is the closed zeta-evaluator span.

The estimate `(3)` is an elementary consequence of those definitions.  Targeted searches of
Burnol's Sonine papers and searches for small-aperture reproducing-kernel asymptotics found no
statement of the exact annihilator-fibre sandwich `(12)`, exponent identity `(13)`, or quadrant
two-sided laws `(16)`--`(17)`.  This is preliminary noncollision, not a priority claim.

Primary references:

- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, J. Théor. Nombres Bordeaux 16 (2004), 65--94,
  <https://arxiv.org/abs/math/0203120>.
- J.-F. Burnol, *On Fourier and Zeta(s)*, Forum Math. 16 (2004), 789--840,
  <https://arxiv.org/abs/math/0112254>.

## Lean decision

The proof uses the literal extended Sonine space, unitary cosine transform, continuous completed
Mellin evaluator, and co-Poisson quotient identification.  None is yet represented in the formal
tree.  Formalizing an abstract geometric-sequence sandwich would duplicate the existing
two-clock detector and would not formalize the mathematical content of `(3)`.  Lean work is
deferred until the Burnol analytic interfaces exist.

## Gates

- [x] extended-Sonine constant/tail split proved
- [x] cosine-reflected left-half estimate proved
- [x] exact off-axis annihilator aperture exponent proved
- [x] exact independent-face asymptotics proved
- [x] generic-estimate route to `(GS24)` closed
- [x] targeted literature noncollision audit
- [ ] construct the surviving source anomaly-cancellation comparison
- [ ] formalize after literal Burnol interfaces exist

