# Factored Gaussian source error

**ID:** completed-arithmetic-forms-gaussian-relative-kernel  
**Stage:** Formalized  
**Type:** Actual-source estimate

For the literal first theta atom, let $q=\pi e^{2x}$,
$F_q(z)=$ `firstAtomNormalizedRotatedPair x z`, and
$$K_q(z,w)=e^{-4z^2-4w^2}F_q(z+w).$$
For $R\ge1$, $q\ge\max(3,4R^2,R^4)$, and $|z+w|\le R$,
$$|K_q(z,w)-e^{8zw}|\le
50e\exp(2e)\frac{R^4}{q}e^{8|z||w|}.$$

With $u=2i(z+w)/\sqrt q$ and $B=(2q-3)^2$, the exact factorization is
$$K_q=e^{8zw}e^E(1-A),\quad
E=-2q(\cosh u-1-u^2/2),\quad A=12q(\cosh u-1)/B.$$
The quartic exponential remainder and $B\ge q^2$ give
$|E|\le2eR^4/q\le2e$ and $|A|\le48eR^4/q$.
Thus $|e^E(1-A)-1|\le50e\exp(2e)R^4/q$.

This source estimate retains the mixed Gaussian factor required for Hermite coefficient
normalization. It does not by itself prove a mixed-rank positivity horizon.

Lean: `CompletedArithmeticForms/GaussianRelativeKernel.lean`.
Capstones: `gaussianRelativeProfile_error_le`,
`firstAtomWickKernel_eq_relativeProfile`, `firstAtomWickKernel_error_le`.
All three depend only on `propext`, `Classical.choice`, and `Quot.sound`.

For $r,s>0$ and $r+s\le R$, two Cauchy estimates give
$$|\partial_z^i\partial_w^j(K_q-e^{8zw})(0,0)|
\le\frac{i!j!}{r^is^j}\,50e\exp(2e)\frac{R^4}{q}e^{8rs}.$$
The Gaussian mixed jet equals $\mathbf1_{i=j}8^ii!$ exactly.
Lean: `CompletedArithmeticForms/WickCauchyPayment.lean`,
`norm_mixedKernelJet_le`, `mixedKernelJet_gaussian`,
`mixedKernelJet_sub`, and `firstAtomWickError_mixed_jet_le`.
Each capstone has the same three standard axioms.

For $r_n=\sqrt{(n+1)/8}$ and $w_n=\sqrt{n!/(n+1)^n}$,
$$\frac{n!}{r_n^n}=w_n\sqrt{8^nn!}.$$
For every $i,j\le N$,
$$w_iw_je^{8r_ir_j}\le e^2(N+1),\qquad r_i+r_j\le\sqrt{N+2}.$$
The proof includes zero degree: $w_n^2\le e(n+1)e^{-n}$ and
$16r_ir_j\le i+j+2$.
Lean: `CompletedArithmeticForms/HermiteRadiusPayment.lean`,
`hermiteContourPairWeight_le`, `hermiteContourRadius_add_le`, and
`hermiteContour_factorial_identity`, each with the same three standard axioms.
