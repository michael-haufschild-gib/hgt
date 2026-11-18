# The energy of the last quotient classes

The class indicators $A_q(n)=\mathbf1_{q\mid n+1}$ satisfy $A_qA_r=A_{\operatorname{lcm}(q,r)}$. Write $D_q$ for their Dirichlet jump symbol. Mellin–Plancherel on $s=\sigma+it$ predicts
$$\int_{\mathbb R}\frac{D_q(s)\overline{D_r(s)}}{|s|^2}\,dt
=\frac\pi\sigma D_{\operatorname{lcm}(q,r)}(2\sigma).$$
The right side follows by integrating $A_q(\lfloor x\rfloor)A_r(\lfloor x\rfloor)x^{-1-2\sigma}$ over $x\ge1$. Cutting the jumps after $M$ replaces $A_q(\lfloor x\rfloor)$ with $A_q(\lfloor x\rfloor)-A_q(M)$ on $x>M$ and zero elsewhere. This bounds the squared norm of the tail divided by $s$ by $\pi M^{-2\sigma}/\sigma$.

At $\sigma>1/2$, put $a=\sigma+1/2$. The weighted measure of cell $[n-1,n)$ is comparable to $n^{-2a}$. After normalizing the cell and class coordinates, the incidence matrix is, up to a bounded invertible diagonal, Dirichlet convolution by $k^{-a}$. Its inverse has coefficients $\mu(k)k^{-a}$. Both are absolutely summable. Thus the normalized classes should form a Riesz basis of the closed span of these cell indicators.

For a fixed $s$ with $\Re s>0$ the nonzero asymptotic $D_q(s)\sim s\zeta(1+s)q^{-s-1}$ gives $\sum_{q\ge2}q^{2\sigma+1}|D_q(s)|^2<\infty$ exactly when $\sigma<\Re s$. A prime wave at its own exponent therefore cannot have a square-integrable representing density for all these class amplitudes. The open ECS question is whether its arithmetic state equation gives such a uniform bound on the actual prime counts. Knowing each fixed-width amplitude separately leaves the harmonic divergence possible.
