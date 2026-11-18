# Reflection of binomial carries at an ordinary prime

For fixed dyadic width $q\ge4$, every fixed finite signed binomial family majorizing the selected Mangoldt levels has linear excess over the log gcd somewhere on every large scale.

For binomials $\binom{(a_i+b_i)n}{a_i n}$ and base $Ln$, take a prime $p\nmid L$. Use $x=Ln\bmod p$ as parameter. For $x\ne0$ the least residues of $ux$ and $-ux$ add to $p\,\mathbf1_{u\ne0}$ for every slope $u\bmod p$. Thus any signed combination $K$ of carries has constant reflected sum $W$. Each pair of slopes $u,v$ contributes its coefficient times $\mathbf1_{u\ne0}+\mathbf1_{v\ne0}-\mathbf1_{u+v\ne0}$. This includes primes dividing either slope or their sum.

The selected prime level is $A(x)=\mathbf1_{p-h\le x<p}$ for $1\le x<p$, with $h=\lfloor p/q\rfloor$. Exactly $h$ reflection pairs have $A(x)+A(-x)=1$. All other pairs have sum zero. Hence
$$\sum_{x=1}^{p-1}|K(x)-A(x)|\ge h|W-1|+((p-1)/2-h)|W|\ge h.$$
Zero attains the last bound. If $K\ge A$ and $p>q$, then $W\ge1$ and the total excess is at least $(p-1)/2-h$. The carry of $\binom{2Ln}{Ln}$ attains this second bound. Both optima concern actual ordinary prime levels and arbitrary real coefficients.

For every sufficiently large $M$, simultaneously for $4\le q\le M$, $1\le L\le M$, and every finite family of real weights and prime-dependent slopes, some $6M\le n<12M$ incurs at least $M/(24q)$ in $\log p$-weighted absolute error at primes $2M<p\le3M$. Each such prime sees a full period on $3p\le n<4p$. Multiplication by $L$ permutes its residues, and the prime number theorem gives $\vartheta(3M)-\vartheta(2M)\sim M$. The family and its size may vary with $M$. [Uniform comparison theorem](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/PrimeLevelErrorsOfFiniteBinomialComparisons.lean)

For a fixed family covering each selected Mangoldt level at all bases $Ln$, the band loss is a lower bound on the signed excess over the selected prime mass. The difference between this mass and the log gcd is $O(\sqrt{qLn})$. Thus the weighted logarithms of the binomials exceed the log gcd by at least $M/(48q)$ at some such base on every large scale. The positive survivors are the exact reflection law, its two sharp per-prime optima, and the lower bound uniform in the slopes and number of terms. [Reflection law and extremizers](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ReflectionOfBinomialCarriesAtAnOrdinaryPrime.lean) · [Actual gcd comparison](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/PrimeLevelErrorsOfFiniteBinomialComparisons.lean)

At $q=4$, selection is the product of two binary carries. Its reflection-even part detects agreement of the bits. Signed cancellation between different prime levels and estimates for this even part remain open.
