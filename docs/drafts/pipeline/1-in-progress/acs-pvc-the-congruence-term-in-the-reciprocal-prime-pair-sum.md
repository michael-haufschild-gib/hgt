# The congruence term in the reciprocal prime pair sum

Let \(I=(M,2M]\cap\mathbb N\), \(M\ge2\). Let \(S_z(h)\) be the Hardy–Littlewood pair singular series restricted to primes through \(z\), including 2. The two-order congruence contribution has a definite sign for every cutoff. On paper, for every \(z\ge 2M\),
\[
  \sum_{d\ne e\in I}\frac{S_z(|d-e|)-1}{de}
  =-\frac{\log M}{2M}+O(M^{-1}).
\]
The constant is uniform in \(z\), so the same formula holds for the full Euler product. The ordinary-prime diagonal has the opposite leading term. Their sum over **any** selection of terminals through \(N\) costs \(O(1+\log N)\). On \(\sqrt N<M\le N\) the congruence term alone contributes \(-3(\log N)^2/16+O(1+\log N)\). The error between the actual distinct-pair covariance and this local prediction remains open. [Ordinary pair sum](acs-pvc-the-noncoprime-part-of-the-ordinary-prime-pair-sum.md)

For the unweighted full series Montgomery and Soundararajan give the distinct-pair term \(-h\log h+Ah+O_\varepsilon(h^{1/2+\varepsilon})\). The reciprocal weights and the moving finite prime cutoff here require the endpoint estimates below. [Montgomery and Soundararajan, equation (16)](https://arxiv.org/pdf/math/0409258#page=4)

**Exact sign at both endpoints (Lean verified).** Independently retain each \(p\le z\) with probability \((p-1)^{-2}\), and let \(q\) be the product of the retained primes. In particular \(2\mid q\). Multiplying the local factors gives \(S_z(h)=\mathbb E[q\mathbf1_{q\mid h}]\). Thus
\[
  \sum_{1\le h\le H}(1-S_z(h))=\mathbb E[H\bmod q]\ge0.
\]
Abel summation preserves this sign against every decreasing nonnegative gap weight. At each left endpoint \(d\in I\), use \(h\mapsto 1/(d+h)\) through \(H=2M-d\). This keeps the strict diagonal exclusion and the last partner. Lean verified the finite prime-insertion recurrence, the nonpositive congruence sum on each sharp reciprocal octave even with a different sieve at every left endpoint, and passage to the full Euler product. [Finite and full endpoint inequalities](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheCongruenceTermInTheReciprocalPrimePairSum.lean#L39) · [Euler product for the full series](../../../../formal/GaloisForLFunctions/BezoutValuationIncidence/HardyLittlewoodSingularSeriesOfTheDampedSource.lean#L282)

**Size of the loss.** Set \(L=\sum_{d\in I}1/d\), \(J=\sum_{d\in I}1/d^2\) and \(L_a=\sum_{d\in I,\ d\equiv a\bmod q}1/d\). The exact two-order sum for fixed \(q\) is
\[
 q\sum_{a\bmod q}(L_a-L/q)^2-(q-1)J.
\]
For \(q\le M\), the counts in two residue classes differ by at most one on every prefix of \(I\). Abel summation gives \(|L_a-L/q|\le 1/M\). For \(q>M\), the exact sum is \(J-L^2\).

Write \(C_z=\prod_{2<p\le z}(1-(p-1)^{-2})\) and \(w(d)=\prod_{p\mid d}(p-2)^{-1}\) on odd squarefree integers, zero elsewhere. Then \(\Pr(q=2d)=C_zw(d)/d\) on products supported through \(z\). To get the constant, factor the Dirichlet series of \(w\) as \(\zeta(1+s)G(s)\). In the coefficients of \(G\), the factor at 2 is \(1-2^{-1-s}\). At an odd prime the coefficients at \(p,p^2\) are \(2/[p(p-2)],-1/[p(p-2)]\). Their absolute logarithmic first moment converges, and \(G(0)=1/(2C_\infty)\). Convolving with \(1/n\) gives \(\sum_{d\le y}w(d)=G(0)\log y+O(1)\) and \(\sum_{d\le y}d w(d)\ll y\). The latter gives \(\Pr(q>M)\ll 1/M\) and \(\mathbb E[q^2\mathbf1_{q\le M}]\ll M\). For \(z\ge2M\), \(C_z/C_\infty=1+O(1/z)\), so \(\mathbb E[q\mathbf1_{q\le M}]=\log M+O(1)\). Inserting these three bounds into the exact sum leaves \(-J\log M+O(1/M)\), where \(J=1/(2M)+O(M^{-2})\).

For the actual diagonal, expand \((\mathbf1_{d\ \mathrm{prime}}\log d-1)^2\). The constant and linear terms cost \(O(1/M)\) by the Chebyshev upper bound. Partial summation of the project's prime estimate gives \(\sum_{M<p\le2M}(\log p)^2/p^2=(\log M)/(2M)+O(1/M)\). No conjecture on joint primality enters this diagonal estimate.

**The distinguished integer residue.** There is a finite model whose value at residue zero is the *actual* reciprocal prime sum. For \(I=(M,2M]\), use the two prime cutoffs \(z_- = \lfloor\sqrt{2M}\rfloor\), \(z_+=M\). Write \(P_z=\prod_{p\le z}p\), \(A_z=P_z/\varphi(P_z)\) and give \(t\bmod P_{z_+}\) uniform measure. Put \(R_z(d,t)=A_z\mathbf1_{(d+t,P_z)=1}-1\). For all large \(M\), Mertens' product theorem gives \(A_-<\log M<\log(2M)<A_+\), since \(1<e^\gamma<2\). Let \(\lambda_d=(\log d-A_-)/(A_+-A_-)\), and set
\[
 F_M(t)=\sum_{d\in I}\frac{(1-\lambda_d)R_-(d,t)+\lambda_d R_+(d,t)}d .
\]
Ordinary factorization gives \(F_M(0)=\sum_{d\in I}(\mathbf1_{d\ {\rm prime}}\log d-1)/d\) exactly. For any fixed integer shift \(t\), moving both endpoints and the reciprocal weights costs \(O_t(\log(2M)/M)\).

On paper the **mean square across all residues** is at most \(\sum_{d\in I}(\log d-1)/d^2\). For the proof, choose one common uniform \(v\in[0,1]\), using the upper sieve at \(d\) when \(v\le\lambda_d\). For fixed \(v\) the sieves are nested as \(d\) increases. CRT gives covariance \(S_{z(d)}(e-d)-1\) for every \(d<e\), since the primes present only at \(e\) have mean factor one. The decreasing partner weight and the sharp prefix sign make the entire off-diagonal nonpositive. The diagonal averages over \(v\) to the stated bound. Jensen’s inequality gives the bound for \(F_M\). Consequently the mean of \(\sum_{m\le K}|F_{m^r}(t)|\) is \(O((1+\log K)^{3/2})\) at squares and \(O(1)\) at sixth powers. Use a common multiple of all the finite periods. [Sparse arithmetic criterion](acs-pvc-sparse-square-and-sixth-power-prime-octaves.md)

**Why the residue average misses the arithmetic input.** Count the reciprocal mass surviving the lower sieve and removed by the upper sieve. Its expectation is \((A_-^{-1}-A_+^{-1})\sum_{d\in I}1/d\asymp 1/\log M\). Its variance is \(O(1/(M\log M))\), by the same sign bound on each sieve separately and the triangle inequality in mean square. Thus the fraction of residues where this mass vanishes is \(O(\log M/M)\). At residue zero it vanishes identically on every octave. A number in \(I\) divisible by a prime from \((\sqrt{2M},M]\) already has a smaller prime divisor. This identifies an explicit rare condition forced by ordinary factorization. Control of the calibrated prime sum at the distinguished residue remains open.

At any residue where the two survivor sets agree, their centered reciprocal sums \(Q_-,Q_+\) satisfy \((Q_++L)/A_+=(Q_-+L)/A_-\). Hence \(\max(|Q_-|,|Q_+|)\ge L(A_+-A_-)/(A_++A_-)\to (\log 2)/3\) as a lower bound. Transferring the global second moment to the origin merely by finding residues reproducing both factorization tests therefore loses the entire power saving. For a pointwise \(M^{-1/6}\) bound this argument would need a fraction of order \(M^{-2/3}\log M\), already larger than the entire agreement set.

Lean verified exact calibration at residue zero, the finite mean-square inequality for every convex mixture of nested sieves, and the finite bound on the proportion of residues with equal survivor masses. Summing at \(d\) uses the forbidden residue \(-t\bmod p\) for the translate \(d+t\). The logarithmic asymptotics for the agreement proportion and the specific choice of interpolation weights remain on paper. [Calibration](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheDistinguishedResidueInThePrimeOctave.lean#L169) · [Finite mean square](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheDistinguishedResidueInThePrimeOctave.lean#L297) · [Agreement bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheDistinguishedResidueInThePrimeOctave.lean#L332)

**The first departures from the integer residue.** For \(M\ge5\) and every integer \(0\le t\le M\), the reciprocal mass removed only by the upper sieve is exactly
\[
 \sum_{\sqrt{2M}<p\le q,\;2M<pq\le2M+t}\frac1{pq-t},
\]
with ordinary primes, squares included once. Every exceptional \(d+t\le3M\) has all its prime factors above \(\sqrt{2M}\) and one at most \(M\). Three such factors would exceed \(3M\). Conversely, in every displayed semiprime both factors are at most \(3M/\sqrt{2M}\le M\), and \(M<pq-t\le2M\). Each factor lies in \((\sqrt{2M},\sqrt{2M}+t/\sqrt{2M}]\), giving a uniform upper bound \((1+t/\sqrt{2M})^2/M\). In particular the two sieves still agree to square-root precision in reciprocal mass for *every* positive translation through \(M^{3/4}\). The calibrated sum there exceeds the ordinary shifted prime reading by a nonnegative correction supported on these semiprimes. Lean verified the pointwise Buchstab identity with the strict lower product cut, the closed upper cofactor cap, and one term for a square. [Translated survivor identity](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheDistinguishedResidueInThePrimeOctave.lean#L397)
