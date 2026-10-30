# Explicit mixed Gaussian horizons for the complete theta source

**ID:** completed-arithmetic-forms-native-gaussian-horizon  
**Stage:** Formalized in Lean 4  
**Type:** Infinite-source error, relative reserve, and simultaneous exhaustion

Write $q=\pi e^{2x}$, $c_0=e^{3\pi}/399$, and $D=e^{4+2e^2}(24+10e^2)$.
The complete native signed moments and their first-atom counterparts, in the same
first-atom mass and Gaussian length coordinates, satisfy
$$|\sigma_k(x)-\sigma_k^{(1)}(x)|\le27\,24^{2k}q^k c_0e^{-3q}
\qquad(q\ge2k+6).$$
This is the exact infinite-source estimate
`RHTower.abs_thetaCuspNativeScaledEvenJet_sub_first_le_effective`, with
`RHTower.regimeOneLikelihoodScale_eq`. The scale condition forces $x>0$.

For $k\le L$ and $q\ge2L+6$, monotonicity of powers gives
$24^{2k}q^k\le24^{2L}q^L$. The exponential series implies
$q^{L+1}e^{-q}\le(L+1)!$, while $e^{-3q}\le e^{-q}$. Consequently
$$
|\sigma_k(x)-\gamma_k|\le\frac{C_L}{q},\qquad
C_L=(2L)!D+27\,24^{2L}c_0(L+1)!,\quad 0\le k\le L.
$$
The Gaussian error and the infinite theta remainder have both been paid explicitly.

Let $G_{N,s}=[\gamma_{i+j+s}]_{i,j<N}$,
$T_{N,s}=\operatorname{tr}(G_{N,s}^{-1})$, and
$A^{\rm nat}_{N,s}(x)=[\sigma_{i+j+s}(x)]_{i,j<N}$.
For $L=s+2N$ and $q\ge2L+6$, the inverse-trace inequality gives
$$
|v^T(A^{\rm nat}_{N,s}(x)-G_{N,s})v|
\le\frac{N T_{N,s} C_{s+2N}}q\,v^TG_{N,s}v.
$$
Thus $q>2N T_{N,s}C_{s+2N}$ leaves a strict half-Gaussian reserve in every vector.
All constants are finite expressions in rank and shift; no fixed-rank limiting threshold
or omitted source atom enters the estimate.

For full signed rank $R$, let $E=\lceil R/2\rceil$, $O=\lfloor R/2\rfloor$, and set
$$
Q_R^{\rm nat}=2(R+1)+6+
2\big[E T_{E,0}C_{2E}+O T_{O,1}C_{1+2O}\big].
$$
The first summand pays both analytic scale domains. The two remaining summands pay the
even and odd mixed heads. Exact parity and the positive first-atom mass/scale congruences give
$$
q(x)\ge Q_R^{\rm nat}\Longrightarrow H_R(s_x^{\rm nat})>0.
$$
An explicit sufficient center is
$X_R^{\rm nat}=\max(0,\frac12\log(Q_R^{\rm nat}/\pi))$.
This is a simultaneous rank–center estimate for the complete pointwise source.
It neither imposes a common center for all ranks nor bounds the compact-center contribution
to the integrated signed hierarchy.

Lean: `CompletedArithmeticForms/NativeGaussianHorizon.lean`,
`nativeScaledEvenJet_firstAtom_error_le_through`,
`nativeScaledEvenJet_gaussian_error_le_through`, `nativeBalancedHead_relative_error_le`,
`nativeBalancedHead_half_posDef_of_scale`, `nativeSignedHead_posDef_of_scale`, and
`nativeSignedHead_posDef_of_horizon`. Their transitive axiom dependencies are exactly
`propext`, `Classical.choice`, and `Quot.sound`.
