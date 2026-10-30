# An explicit Gaussian horizon for first-atom moments

**ID:** completed-arithmetic-forms-effective-gaussian-horizon  
**Stage:** Formalized in Lean 4  
**Type:** All-order source approximation and quantitative positivity

Let $q=\pi e^{2x}\ge3$, $B=(2q-3)^2$, $C=4q^2e^{x-2q}$, and
$g_x(z)=C e^{-2q(\cos(2z)-1)}[B-12q(\cos(2z)-1)]$.
The literal first-atom mass is $f_1(x)^2=CB>0$.
Put
$$
F_x(z)=\frac{g_x(z/\sqrt q)}{f_1(x)^2},\qquad
D=e^{4+2e^2}(24+10e^2).
$$
On $|z|\le1$, write $w=2iz/\sqrt q$, $a=-2q(\cosh w-1)$, and $b=4z^2$.
The exponential Taylor remainders at $w$ and $-w$ give
$$
|\cosh w-1-w^2/2|\le |w|^4e^{|w|}/24.
$$
Since $|w|\le2$ and $w^2/2=-2z^2/q$,
$$
|a-b|\le\frac{4e^2}{3q}\le\frac{2e^2}{q},\qquad |b|\le4.
$$
The identity $e^a-e^b=e^b(e^{a-b}-1)$ and the first-order exponential remainder imply
$$|e^a-e^b|\le e^{4+2e^2}\frac{2e^2}{q},\qquad |e^a|\le e^{4+2e^2}.$$
Also $B\ge q^2$ and
$$
\left|\frac{12q}{B}(\cosh w-1)\right|
\le\frac{24+8e^2}{q^2}.
$$
Splitting $F_x-e^b$ into its exponential error and affine-factor error yields
$$\sup_{|z|\le1}|F_x(z)-e^{4z^2}|\le D/q.$$

Cauchy's estimate on the unit circle therefore bounds every literal normalized signed moment:
$$
\left|\frac{(-1)^k f_{1,x}^{(2k)}(0)}{f_1(x)^2q^k}
       -\gamma_k\right|
\le \frac{(2k)!D}{q},\qquad
\gamma_k=16^k(\tfrac12)_k=\frac{4^k(2k)!}{k!}.
$$
Here $f_{1,x}(t)=f_1(x+t)f_1(x-t)$, so the derivatives are the actual reflected source jets.
If $q>D K!$, then for every $k\le K$ the error is strictly smaller than
$(2k)!/k!\le\gamma_k$. Thus $K<\nu(x)$, where $\nu(x)$ is the least negative signed moment order.
An explicit sufficient center is
$$
X_K=\max\left(0,\frac12\log\frac{D K!+1}{\pi}\right),\qquad
x\ge X_K\Longrightarrow K<\nu(x).
$$
The bound is simultaneous in center and order. It does not assert a lower bound for the least
nonpositive mixed Hankel rank: positivity of individual moments does not imply positivity of
their mixed quadratic form. The infinite theta remainder requires its own quantitative transfer.

Lean: `CompletedArithmeticForms/FirstAtomGaussianHorizon.lean`,
`firstAtomGaussianKernel_error_le`, `firstAtomNormalizedRotatedPair_error_le`,
`firstAtomScaledEvenJet_gaussian_error_le`, `firstAtom_signed_moment_pos_of_scale`,
`firstAtomNegativeOrder_gt_of_scale`, and `firstAtomNegativeOrder_gt_of_horizon`.
Their transitive axiom dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.
