# Boundary Fourier power of a confined state

- **Stage:** 3-formalized
- **Source:** [QIC](../../../reports/rh-current-frontier-map.md#qic)
- **Lean:** [IsConfinedNullVector.strip_laplace_product](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheBoundaryFourierPowerOfAConfinedState.lean#L98) · [boundary_poisson_identity](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheBoundaryFourierPowerOfAConfinedState.lean#L145) · [halfPlane_laplace_decay](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/TheBoundaryFourierPowerOfAConfinedState.lean#L269)

For every confined null state $F$ with confinement coefficient $a>0$, every $y\in\mathbb R$ satisfies
$$
\frac a2|LF(-4+iy)|^2+
\sum_{\gamma}|LF(i\gamma)|^2\frac{4}{16+(y-\gamma)^2}
=-\Re\sum_{z\ {\rm off}}\frac{LF(z)LF(-z)}{4+iy-z}.
$$
All sums count multiplicities. If the off-line divisor is finite, including the lone-quartet case, then $|LF(-4+iy)|^2\le C_F/(1+y^2)$ at every frequency.

**Proof.** The [unit tilt](../3-formalized/qic-absolute-zero-traces-of-every-confined-state.md) gives $e^{-5u}F\in L^2$ on the negative ray, so $g(u)=e^{(-4+iy)u}F(u)$ is integrable by Cauchy–Schwarz. Set $C(t)=\int g(u)\overline{g(u+t)}\,du$. Fubini gives $\int C=|\int g|^2$ and translation gives $C(-t)=\overline{C(t)}$. Thus $2\Re\int_0^\infty C(t)\,dt=|LF(-4+iy)|^2$.

For $t\ge0$, the translated null equation identifies $-aC(t)$ with the translated zero pairing multiplied by $e^{-(4+iy)t}$. Absolute summability of the reflected products and $|\Re z|<1/2$ justify integration over the entire ray. Each copy gives $LF(z)LF(-z)/(4+iy-z)$. Taking real parts gives the identity. The critical-line sum is nonnegative. At $y$ and $-y$ its omission bounds the power by the norm of the paired off-line transform, which is $O_F((1+y^2)^{-1})$ by the [paired Cauchy kernel bound](../3-formalized/qic-poisson-bound-on-the-critical-line-traces.md).

More generally, write $Z(p)=\sum_z LF(z)LF(-z)/(p-z)$ over all copies. For $3<\Re p<5$ both $e^{(p-8)u}F(u)$ and $e^{-pu}F(u)$ are integrable. Applying the same split to their correlation gives
$$Z(p)+Z(8-p)=-a\,LF(p-8)LF(-p).$$

For finitely many off-line zeros, there is a single $K_F$ such that $|(w+5)LF(w)|\le K_F$ on $\Re w\ge-4$. Indeed $L(z)=LF(z-4)$ is bounded and holomorphic on the open right half-plane and continuous up to its boundary. The Fourier bound above gives $|(1+iy)L(iy)|\le K_F$. For $r>0$ the holomorphic function $(1+z)L(z)/(1+rz)$ is bounded on the closed half-plane and has the same boundary bound. The half-plane maximum principle gives that bound in the interior. Let $r\downarrow0$.
