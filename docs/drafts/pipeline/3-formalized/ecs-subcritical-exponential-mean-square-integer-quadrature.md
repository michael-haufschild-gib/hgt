# Exponential mean square of the integer quadrature error

For $0\le\lambda<1/2$, the critical-state integer quadrature error $e^{\lambda t}(N(t)-Ae^{t/2})$ belongs to $L^2(\mathbb R)$.

Set $s=1/2-\lambda+i\xi$, $\Psi_\lambda(u)=e^{\lambda u}\Phi(u)$ and $H_\lambda(v)=e^{(\lambda-1/2)v}(\lfloor e^v\rfloor-e^v)$. The function $H_\lambda$ is integrable at both ends. Its Fourier transform is the fractional-part Mellin integral $\zeta(s)/s$. As distributions the weighted lattice-minus-continuum measure is $(\partial_v+1/2-\lambda)H_\lambda$. The resulting Parseval identity is
\[
 \int_{\mathbb R}e^{2\lambda t}|N(t)-Ae^{t/2}|^2dt
 =\frac1{2\pi}\int_{\mathbb R}|\zeta(1/2-\lambda+i\xi)\,\mathcal L\Phi(\lambda-i\xi)|^2d\xi .
\]
The tilted state has $\|\Psi_\lambda-\Psi_\lambda(\cdot+h)\|_2^2=O(h/\log(1/h))$ by the wall law, boundedness of the weight on the negative ray and an $O(h)$ weight increment in norm. A dyadic Fourier annulus at height $Y$ then has energy $O(1/(Y\log Y))$, by testing the increment at $h=1/Y$ in angular frequency, where $|1-e^{ih\xi}|$ has a fixed positive lower bound on that annulus. Hence every squared Fourier weight $(1+|\xi|)^{2r}$ is integrable for $r<1/2$. Zeta convexity gives growth exponent $1/4+\lambda/2+\varepsilon<1/2$. The physical primitive removes the need to differentiate $\Phi$. Write $D=N-Ae^{t/2}$. Fubini gives
\[
 B(t)=e^{(\lambda-1/2)t}\int_{-\infty}^te^{u/2}D(u)du=(H_\lambda*\Psi_\lambda)(t).
\]
Indeed, a substitution in each integer atom leaves the number $\lfloor e^{t-v}\rfloor$ of contributing indices. Exponential confinement dominates the absolute integrals. Thus $B$ is continuously differentiable and $B'+(1/2-\lambda)B=e^{\lambda t}D$. Both convolution factors are integrable and $B\in L^2$. The zeta multiplier estimate gives $\xi\widehat B\in L^2$. Plancherel bounds the $L^2$ norms of the difference quotients of $B$ uniformly, since $|e^{ih\xi}-1|\le |h\xi|$. Fatou at $h\downarrow0$ then puts $B'$ in $L^2$. For fixed $\lambda<1/2$ take a second tilt $\lambda<\mu<1/2$. Cauchy–Schwarz against $e^{-(\mu-\lambda)t}$ on $t>0$ now puts $e^{\lambda t}D$ in $L^1$ there. On $t<0$ the confined atom sum gives $N(t)=O(e^{2t})$, so the negative ray is absolutely integrable as well. The differential identity gives $B'\in L^1$. Classical Fourier integration by parts then gives $\widehat {e^{\lambda t}D}=\zeta(s)\widehat{\Psi_\lambda}$ pointwise, and Plancherel gives the stated equality. [Physical primitive in Lean](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheFloorPrimitiveOfTheIntegerReference.lean) · [Fractional-part Mellin integral](../../../../formal/GaloisForLFunctions/RHTower/FractionalPartZeta.lean).

**Lean.** `riemannHypothesis_or_integer_quadrature_parseval` gives both the physical square bound and the exact frequency integral simultaneously for all subcritical tilts. The proof uses `criticalState_tilted_fractional_fourier_energy`, `squared_zeta_on_positive_line` and `integrable_square_derivative_of_fourier_moment`. [Exact Parseval identity](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/ParsevalForTheIntegerQuadrature.lean).
