# Finite arithmetic readings of the complete Green operator

For fixed overlap $c>0$, let $A_N$ be the literal complete tilted-spline Weil
matrix and $r_{m,N}$ the normalized Ramanujan vectors. The inverse-tail target is
\[
\forall\varepsilon>0\ \exists S\subset\mathbb N_{>0}\text{ finite}\quad
\|A_N^{-1}v\|\le\varepsilon\|v\|
\]
eventually in $N$, for every $v$ orthogonal to all $r_{m,N}$ with $m\in S$.
This controls every unobserved direction of the actual inverse. Fixed-packet
entry limits alone do not imply it.

The actual source reserve has the form
$a\|x\|^2+\beta D_N(x)\le\langle A_Nx,x\rangle$, $\beta>0$.
For each finite $T$, the complete energy sublevel
$\|x\|=1$, $\langle A_Nx,x\rangle\le T$ therefore has a finite coordinate
certificate $\sum_{m\in S}|\langle x,r_{m,N}\rangle|^2\ge1/18$.

Put $u=A_N^{-1}v$. If $\|v\|=1$ and $\|u\|>\varepsilon$, then
$x=u/\|u\|$ has complete energy at most $1/\varepsilon$.
For an unread vector $v$,
\[
\langle u,r_{m,N}\rangle
=\langle v,A_N^{-1}r_{m,N}-E_m(c)^{-1}r_{m,N}\rangle.
\]
Thus the norm residuals of the actual inverse modes force every coordinate
in the finite certificate to vanish, contradicting its positive mass.
The quantitative finite-certificate choice is
$\delta=\varepsilon/[6(|S|+1)]$, for which
$|S|\delta^2/\varepsilon^2<1/18$.

An operator-norm approximation by the explicit arithmetic Green sum
$\sum_{m\in S}E_m(c)^{-1}r_{m,N}\otimes r_{m,N}$ additionally requires
the finite Gram payment. That approximation must retain the actual inverse
on every horizon direction.

Source statements: `MacroscopicOverlapSpectralAssembly`,
`TheCompleteWeilFormIsPositiveAtEveryFixedOverlap`, `WeilGreenModes`.
