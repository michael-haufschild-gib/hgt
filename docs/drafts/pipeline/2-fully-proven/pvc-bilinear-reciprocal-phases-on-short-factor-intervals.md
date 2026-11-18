# Bilinear reciprocal phases on short factor intervals

**PVC · Paper theorem.** Let $P,V\ge1$, $J=[a,b)\subset[V,2V)$, $H=b-a>0$, $Z>0$, and $h\ne0$ an integer. Restrict $P\le p<2P$, $v\in J$ by any product cutoff $L<pv\le U$. For arbitrary complex coefficients, put
$$
S_h=\sum_p\alpha_p\sum_v\beta_v\,e(hZ/(pv))\mathbf1_{L<pv\le U},
\quad u=Z/(16P^3V^2),\quad w=ZH/(4P^3V^2).
$$
Then
$$
|S_h|^2\le\|\alpha\|_2^2\|\beta\|_2^2
\bigl(P+H(64P\sqrt w+12/\sqrt u)\sqrt{|h|}\bigr).
$$

**Proof.** Cauchy–Schwarz in $p$ removes the first coefficients. Expanding the second moment gives one correlation for each $m,n\in J$. The two product restrictions intersect in a sharp interval of $p$. For $m<n$ the phase is $hZ(n-m)/(mnp)$, with reciprocal curvature parameter $Z(n-m)/(4mnP^3)$ between $u$ and $w$. The [integer harmonic estimate](../../../../formal/GaloisForLFunctions/PrimeExponentialSums/FractionalPartsOnIntegerReciprocalBlocks.lean) bounds its sum by $(64P\sqrt w+12/\sqrt u)\sqrt{|h|}$. Conjugation covers $n<m$. The diagonal is at most $P$. The [finite symmetric Schur bound](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/RiemannXiSuzukiGramSchur.lean) gives the stated inequality.
