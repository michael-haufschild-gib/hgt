# Strict seam reserves and a quantitative source neighborhood

**ID:** completed-arithmetic-forms-seam-coercivity  
**Stage:** Formalised in Lean 4  
**Type:** Radical classification and relative reserve for the complete theta tail

Let $\Phi$ be the complete theta source and
$U_k(r)=\int_{s>r}h_k(s/2)\,ds$ its signed native jet tail.
The exact seam identity is
$$\sum_{i,j<N}v_iv_jU_{i+j}(0)
=\int_{\mathbb R}\left|\sum_{j<N}v_j(2i)^j\Phi^{(j)}(x)\right|^2dx.$$

Every finite family $\Phi,\Phi',\ldots,\Phi^{(N-1)}$ is linearly independent.
Indeed, integration of a vanishing derivative combination against $x^k$ is
triangular in the coefficients:
$$\int x^k\Phi^{(j)}(x)\,dx
=(-1)^j(k)_{\!j}\int x^{k-j}\Phi(x)\,dx,$$
with zero value for $j>k$ and diagonal
$(-1)^k k!\int\Phi\ne0$. Successive polynomial moments recover every
coefficient. The same conclusion holds for complex coefficients by taking
real and imaginary parts. All polynomially weighted derivative integrals
exist by the literal source's exponential decay.

Thus a nonzero $v$ gives a continuous derivative packet nonzero at some point.
Its squared norm is integrable: the packet is integrable and bounded, so its
square is bounded by a constant times its norm. Its square integral is strictly
positive. Consequently the complete seam matrix
$$S_N=[U_{i+j}(0)]_{i,j<N}$$
is positive definite at every finite rank and has zero radical.

Put $K_k=$ `thetaCuspNativeJetDecayConstant k` and
$D_N=\sum_{k\le2N}K_k$. For $r\ge0$, the exact tail difference and native
decay give
$$|U_k(r)-U_k(0)|
=\left|\int_0^r h_k(s/2)\,ds\right|\le rK_k.$$
Hence the entire rank-$N$ tail head has relative seam cost
$$\eta_N(r)=rN D_N\operatorname{tr}(S_N^{-1}).$$
In the explicit interval
$$0\le r\le\frac{1}{2(1+N D_N\operatorname{tr}(S_N^{-1}))},$$
this cost is strictly below $1/2$, leaving
$$H_N(U(r))-\tfrac12S_N>0.$$
The reserve concerns the complete theta source at every order.

If $r\ge2\,\mathrm{nativeMixedHorizon}(N)$, every native full head at center
$s/2$, $s>r$, is strictly positive. Integrating any nonzero vector's positive
quadratic form over that half-line gives $H_N(U(r))>0$. Each entry is integrable
by the native decay bound. Thus the two explicit source regions are
$$0\le r\le[2(1+N D_N\operatorname{tr}(S_N^{-1}))]^{-1}
\quad\text{and}\quad r\ge2\,\mathrm{nativeMixedHorizon}(N).$$
Positivity through the intervening compact interval requires an additional
compensation estimate. The seam and distant-tail estimates themselves have
no aperture parameter and retain the complete source.

Lean: `GaloisForLFunctions/CompletedArithmeticForms/SeamCoercivity.lean`.
The capstones are `thetaDerivativePacket_coefficients_eq_zero`,
`thetaSeamPacket_eq_zero_iff`, `nativeTailHead_zero_posDef`,
`nativeSignedJetTail_seam_error_le`, `nativeTailHead_seam_relative_error_le`,
`nativeTailHead_half_posDef_of_seam_radius`, and `nativeTailHead_posDef_of_horizon`.
Their transitive axiom dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.
