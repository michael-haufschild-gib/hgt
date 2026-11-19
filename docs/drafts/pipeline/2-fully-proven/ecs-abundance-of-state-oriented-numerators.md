# Abundance of state-oriented common numerators

Put $X=e^T$, $L=\lceil X^{1+\eta}\rceil$ and $m=\int\Phi$. If RH fails, there are fixed $c,g,d>0$ such that for every $0<\eta\le1$, every sufficiently late test on its original §2.16 sequence has a measurable set $E$ of displacements and a finite set $N\subset[X,L^2)$ with
$$
 R(\Phi)-R(\mathbf1_{E^c}\Phi)<-cX^g,\qquad
 L\sum_{H\in N}H^{-1}>cX^{g+1/2},\qquad L\,\#N>cX^{g+3/2}.
$$
Every such numerator satisfies $H^{1/2+d}<L$. Taking $0<\eta<\min(g,1)$ gives $\#N\gg X^{1/2+g-\eta}$. Here $R$ is the signed finite ordinary band on the original time interval, with outer multiplier $m$ fixed. Every $v\in E$ selects an $H\in N$ at one of its own binary digits, and each $H\in N$ occurs at such a displacement. The interior sign is opposite $m\Phi(v)$. The interior and its compensating flank retain opposite factorial discrepancies on every nonempty subset of each allowed terminal block of width $H^{1/2+d}$. Each side supplies the §2.16 runs of ordinary Chebyshev increments for that block.

**Proof.** Write the original band as $\int m\Phi(v)Q(v)\,dv$ by translating its finitely many atoms. Here $Q(v)$ is the fractional prime discrepancy over the active denominators divided by $\sqrt{e^{T-v}}$. The active denominators are cut out by Borel inequalities, so $Q$ is measurable. The diagonal-band theorem gives $R(\Phi)\le -AX^g+O_\Phi(1)$ along the same tests as the exterior gain. Put $M=|m|\int|\Phi|$ and $B=AX^g/[32(M+1)]$. Take
$$
 E=\{v:m\Phi(v)Q(v)<-8B|m|\,|\Phi(v)|\}.
$$
On its complement integration gives $R(\mathbf1_{E^c}\Phi)\ge-8BM$. Consequently the signed contribution of $E$ is less than $-AX^g/2$ eventually.

At **each** $v\in E$ the binary doubling identity selects an adverse digit. Removing denominators at or below $\sqrt H$ costs at most $(1+\log 4)\sqrt H$. The remaining active interval has discrepancy larger than $B\sqrt H$. Its endpoints give $X\le H<L^2$ and $H^{g/6}\le X^g$. Completing the odd-quotient row forces the opposite sign on one flank. The divisor variation estimate preserves both signs on every subset of each terminal block for $d=\min(g/12,1/4)$. The quotient-cell subdivision and trimming estimates then give the opposite runs on that same block. Take the longest such block, of integer width $D=\lfloor H^{1/2+d}\rfloor$. On the interior short interval choose its last denominator $y\le L$. Its fixed quotient $q$ gives $qy\le H-D\le H<(q+1)y$, so $D<y$ and $H^{1/2+d}<L$. All estimates are uniform in $v,H$ once $T$ is large.

Let $N$ contain precisely the numerators in this range admitting such a witness from $E$. The signed removal bound gives $AX^g/2<C_\Phi LX^{-1/2}\sum_{H\in N}1/H$. Since $H\ge X$, the sum is at most $\#N/X$. Decreasing $c$ gives all three bounds. An upper bound for this actual family, or sufficient signed cancellation on its displacements, remains open. [Programme §2.16](../../../reports/review-1911/obstacles-summary.md#216-programme-to-close-ecs).
