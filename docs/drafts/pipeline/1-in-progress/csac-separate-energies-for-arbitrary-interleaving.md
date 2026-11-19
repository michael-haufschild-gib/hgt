# Power threshold and exhaustion of interleaving supports

For positive nondecreasing conductor weights $r$ with $1/r\in\ell^2$, a cutoff-independent bound on the weighted cells and integrated half-jet is equivalent to $w/r\in\ell^2$. [Sharp integral criterion](../3-formalized/csac-separate-conductor-energies-on-arbitrary-interleavings.md)

For two pairs of truncations, bilinearity splits the difference into the lower tail against one upper section and the other lower section against the upper tail. The same bound, with $A_N,B_N$ replaced by their infinite limits, therefore gives convergence of both quotient variation and jet norm on $\ell^2_r\times\ell^2_r$. Normalized rounded integer conductors converge in $E_r$ by domination. Their terminal differences are the required integral endpoint jumps.

More precisely, for the fixed lower atom the positive cells are $2v_1-v_2,v_2-v_3,\ldots,v_N$, with the first entry $2v_1$ when $N=1$. The exact real operator norm into weighted variation is $\sqrt{(2w(1)/r(1))^2+\sum_{k=2}^N((w(k)+w(k-1))/r(k))^2}$. The triangle bound is attained by alternating signs with magnitudes proportional to the corresponding weight divided by $r(k)^2$. Integer scalings and rounding attain the same supremum.

For the de la Vallée Poussin price, a single integral family detects every $s<3/2$ without rounding. Take $u=\delta_1$ and $v_k=(-1)^k$ on $(K,2K]$, zero elsewhere. Then $|C_k|=2$ in the interior. Its variation is at least of order $K^2\exp(-c\sqrt{\log(2K)})$, while the product of the individual norms with $r(k)=k^s$ is at most of order $K^{s+1/2}$ for $s\ge0$. The ratio diverges for every $s<3/2$.
