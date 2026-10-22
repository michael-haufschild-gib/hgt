# SQB: actual Hardy responses with the native arithmetic weight

- **ID:** SQB104
- **Stage:** 1-in-progress
- **Type:** CANDIDATE, with analytical source identifications below
- **Source:** [native source comparison](../../sqb-native-spectral-source-comparison.md)
- **Statement:** Normalize the literal common-forcing theta responses into the half-shift Hardy model space while retaining their full native norm and forcing.

## Goal and status

The common-forcing branch requires normalized packets whose full native residual tends to zero while their native mass survives. The positive scattering kernel is useful only after its quadratic form is compared with that native norm. The construction below identifies the actual responses and their weight; it does not prove the required estimate. The alternative chain through all-degree signed theta moments remains open and is not identified with this Hardy form.

The arguments below are paper derivations from the indicated source theorems. They have not been Lean-checked or promoted to formalized status. No Lean build or computation accompanies this card.

## Actual responses in the Hardy model space

Use the right-half-plane coordinate `lambda`, and put

```text
E0(lambda) = xi(1+lambda),
S(lambda)  = xi(lambda)/E0(lambda),
G(lambda)  = xi(1/2+lambda)/E0(lambda),
f_q(lambda) = profileTransform(q,-i*lambda)/E0(lambda).
```

The last definition uses the actual entire integral, including removed points. The proved `profile_transform_equation` gives

```text
f_q(lambda) = G(lambda)/(lambda^2+alpha_q^2)
```

away from the displayed denominator's zeros. Entireness of the literal response removes those poles. Nonvanishing of `xi` on `Re>=1` makes `f_q` analytic near every point of the closed right half-plane. No critical-line assumption enters.

**Uniform Hardy bound.** Write `lambda=x+it`. For large `|t|`, uniformly over `0<=x<=1`, the completed-zeta identity expresses `G` as

```text
pi^(1/4) * ((lambda+1/2)*(lambda-1/2)/(lambda*(lambda+1)))
  * Gamma((lambda+1/2)/2)/Gamma((lambda+1)/2)
  * zeta(lambda+1/2)/zeta(lambda+1).
```

The rational factor is uniformly bounded there. `GammaVerticalRatioBetaBound.norm_Gamma_vertical_le`, with Gamma shift `1/4`, bounds the Gamma quotient by its real-axis value. The Beta integral bounds that real ratio uniformly for real part at least `1/4`: its integrand decreases as that real part increases. `norm_riemannZeta_le_sqrt_norm_add_two_half` gives an `O(|t|^(1/2))` numerator bound. `norm_inv_riemannZeta_shift_le` gives an `O(log^7|t|)` reciprocal bound independent of `0<x<=1`; continuity supplies `x=0` away from the zeta pole. The entire completed quotient handles the compact region containing that pole.

For fixed `q`, choose the tail beyond twice the magnitudes of the two roots of `lambda^2+alpha_q^2`, and beyond unit height. Its denominator is then bounded below by a constant times `t^2`. Consequently

```text
|f_q(x+it)| <= C_q * |t|^(-3/2) * log^7|t|   (0<=x<=1, large |t|).
```

For `x>=1`, absolute Dirichlet convergence bounds the zeta numerator uniformly, and `norm_riemannZeta_ge_of_two_le_re` bounds the reciprocal denominator. The same Beta estimate bounds the Gamma ratio. The polynomial prefactor is bounded, and the actual roots have real parts of magnitude less than `1/2`. Thus the remaining rational denominator gives a uniform `O_q((1+t^2)^(-1))` bound in this half-plane. On the compact region omitted from the first strip estimate, continuity of the entire response quotient supplies a uniform bound. Squaring and integrating these majorants proves

```text
sup_(x>0) integral_R |f_q(x+it)|^2 dt < infinity.
```

**Model-space membership.** The existing `norm_scatteringCore_le` and `norm_boundaryPhase` source identities show that `S` is an inner function of this half-plane. Let `q*` denote a Xi copy with spectral parameter `conj(alpha_q)`, available from Xi's real-entire symmetry. On the boundary, functional equation and conjugation give

```text
S(it)*conj(f_q(it)) = f_(q*)(it).
```

Both sides' analytic representatives satisfy the Hardy bound just proved. For any right-half-plane Hardy function `g`, the boundary integral of `f_(q*)*g` is zero, by the Hardy product/Cauchy identity. Hence `<f_q,S*g>=0`. Therefore every actual `f_q` belongs to `K_S = H2 orthogonal-to S*H2`. This gives an actual source family in the positive-kernel space, with its reflected partner retained.

## Exact native weight and forcing

On the boundary define

```text
W(t) = |xi(1+it)|^2 * boundaryWeight(t),
<u,v>_W = (1/pi)*integral_R conj(u(t))*v(t)*W(t) dt.
```

This weight is nonnegative and bounded, and tends to zero at large frequency, by the proved boundary-weight bound and Xi vertical decay. It is not replaced by the unweighted Hardy norm. For copies in the upper squared-energy chamber, the existing `SelbergThetaCommonForcingPacketMass.gram_eq_integral` already gives

```text
gram(q,r) = <f_q,f_r>_W.
```

Indeed `f_q(it)=-Xi(t)/(xi(1+it)*(t^2-alpha_q^2))`; the shifted Xi factor cancels against `W`, leaving the literal native density `N=Xi^2*boundaryWeight`. A direct source-pairing argument below gives the same identity on paper for all copies, without dividing by energy differences. This all-copy extension is not an existing Lean conclusion.

**Direct bilinear source argument.** Let `p,r` belong to the finite complex span of `Phi` and the actual profiles, allowing their conjugates. These profiles are even: their admitted Fourier transforms are even, and Fourier injectivity transfers that equality back to the profiles. They have all exponential moments, their height seeds have all-power bounds, and their periodizations are globally bounded by a constant times `positiveSource`. Write `P_p` for periodization of `sqrt(y)*p(log(y)/2)` and `pHat` for the angular-frequency Fourier transform. Absolute unfolding gives the native bilinear pairing from the seed `p` and the horizontal mean of `P_r`.

The general `SelbergThetaEisensteinProbes.profile_eisenstein_pairing` supplies the latter mean's Mellin transform first at real parameters greater than one. Both sides extend holomorphically to the corresponding complex half-plane. For the horizontal Mellin integral, its absolute integrand is bounded by a constant times the original positive horizontal source; the already admitted Mellin integrals at two neighboring real abscissas dominate it and its logarithmic derivatives on compact parameter sets. The transform expression is holomorphic there by entireness and the zero-free denominator. The identity theorem therefore gives the complex Mellin formula. In the contour coordinate used by the scalar source theorem, it is

```text
M_r(z) = rHat(-i*(z+1)) * (1+(z+2)/z*scatteringCore(z)).
```

Bilinear Fourier duality now gives the uncentered pairing as twice the quarter-line vertical integral of `M_r(z)*pHat(-i*(z+1))`. This assertion is bilinear; use `conj(p)` as the first profile for the Hermitian form. For this finite profile class the entire transforms have uniform exponential decay on the contour strip: `Phi` gives Xi, and each response gives its entire quadratic divided difference. At large frequency the rational denominators are uniformly separated; removed points lie in a compact region. Thus both vertical sides are absolutely integrable, horizontal sides tend to zero, and the only crossed pole is `z=0`. Its residue is `pHat(-i)*rHat(-i)/xi(2)`. Reflection averages the boundary phase, since both transforms are even. Consequently

```text
integral P_p*P_r
  = 2*pHat(-i)*rHat(-i)/xi(2)
    + (1/pi)*integral_R pHat(t)*rHat(t)*boundaryWeight(t) dt.
```

The original means are `integral P_p=2*pHat(-i)` and `V=2*xi(2)`. Subtracting their exact product divided by `V` cancels precisely the displayed residue. Replacing `p` by `conj(p)` proves the centered Hermitian identity. Taking the two actual profiles proves `gram(q,r)=<f_q,f_r>_W` at all copies, including real and reflected energy collisions. The proof retains both Weyl terms and every primitive row; it does not assume an abstract spectral Plancherel formula.

The forcing has a matching boundary function `F0(t)=-G(it)/4`. The already proved centered scalar formula gives `<F0,f_q>_W=m(q)`. Pointwise algebra gives the full image, retaining this forcing:

```text
e_q*f_q(it)+F0(t) = ((1+t^2)/4)*f_q(it),
e_q=(1+alpha_q^2)/4.
```

The forcing/forcing entry is the same direct bilinear argument with both profiles equal to `Phi`. It gives

```text
||nativePositive||^2
  = 2*C*xi(3/2) + (1/pi)*integral_R N(t) dt,
C=xi(3/2)/xi(2).
```

Here the contour integrand is `symbol(z)*xi(z+3/2)`. The already proved Xi strip decay admits both vertical sides and kills the horizontal sides. Its sole crossed pole is `z=0`, with residue `C*xi(3/2)`. Reflection replaces the phase by `boundaryWeight`. The exact native mean identity `M^2/V=2*C*xi(3/2)` therefore yields

```text
||forcing||^2 = (1/(16*pi))*integral_R N(t) dt = ||F0||_W^2.
```

This argument specifies the new seed substitution; the existing q-specific scalar theorem cannot itself be applied to `Phi`. The bilinear extension, Hardy admission and resulting forcing-norm theorem remain to be formalized. Together with the vector and mixed entries, the paper identity preserves the augmented Gram of vectors, images and forcing for all actual copies.

In particular, for an actual finite domain packet `V=sum_i c_i*v_qi`, put `f=sum_i c_i*f_qi`. The complete image identity and augmented Gram give the paper estimates

```text
||(A-z)V||^2 = (1/pi)*integral_R W(t)*|((1+t^2)/4-z)*f(it)|^2 dt,
Re <V,(A-1/4)V> = (1/(4*pi))*integral_R t^2*W(t)*|f(it)|^2 dt >= 0.
```

All integrals are admitted by the same removed-point continuity and exponential native density bounds. This is a quarter-energy bound on the literal theta packet family, not on arbitrary native Maass vectors. The individual packet equation still has the nonzero forcing; the estimate does not turn its parameter into an eigenvalue.

## Consequence for the hard estimate

The source comparison is now an explicit weighted problem on actual Hardy model-space responses. The unweighted kernel's positivity does not remove `W`, and the forcing `F0` is retained in the weighted space; no unweighted Hardy admission for `G` is asserted. A source-derived estimate must control the weighted packet residual and its mass, or identify a sufficient weighted form with the all-degree theta current. Neither has been obtained here.

The boundary diagonal of the earlier phase kernel is also explicit. For `b(lambda)=S(lambda)/B(lambda)` and `B(lambda)=(lambda-1)/(lambda+1)`, differentiation at `lambda=it` gives `K_b(it,it)=h(t)` and

```text
(K_b + 2/((lambda-1)*(conj(mu)-1)))(it,it)
  = h(t)+2/(1+t^2) = 2*Re(xi'(1+it)/xi(1+it)).
```

Thus integrating the diagonal retains a multiplication weight; it does not perform the rank-one projection appearing in the full kernel. The actual Hardy source map above is the positive construction exposed by this comparison. No route is retired and no RH implication is declared closed.

## Verification boundary

- Source signatures and relevant proof bodies were read for the Gamma Beta bound, uniform shifted reciprocal-zeta bound, square-root zeta bound, complete response transform, native Gram, mean cancellation and scalar contour construction.
- Broad, deep and method-view searches covered boundary kernels, variance/Dirichlet forms, Carleson mechanisms and actual Hardy responses. Several searches were partial; compiler metadata was mostly pending and semantic coverage was incomplete or unreported. Search output is discovery evidence, not verification of this construction.
- [x] Source-specific construction and paper estimates stated.
- [ ] Native Hardy admission and forcing-norm identities checked in Lean with bounded leaf checks.
- [ ] Complete weighted source estimate yielding SQB occurrence or all-rank orientation.
- [ ] Unconditional RH proof.
