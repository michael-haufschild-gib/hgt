# Separate real Weil energies for aligned divisibility sieves

Fix a common modulus $q$. At the upper endpoint $qm$ give lower graph $i$ the signed integer multiplicity $w(i)=\sum_t a_t(\mathbf1_{d_t\mid i}-\mathbf1_{q\mid i})$, where $d_t r_t=q$. Set $L=\sum_t|a_t|$. Deleting every $q$-th graph is the case $d_1=1$, $a_1=1$. Reindexing the multiples of $d_t$ shows that the actual pole product minus prime order is $\sum_t a_t[A(r_tm)-A(m)]$, with $A(m)=mH_m-\log(m!)$.

Write $K_w(m)$ for its second difference in $m$. For $m\ge1$ and square-summable real endpoint sequences $u,v$, put $E_m(u)=\sum_{i,j}u_i u_j[D_1(m+i+j-1)-D_1(m+i+j)]$. Then
$$
\left|\sum_{i,j}u_i v_j K_w(m+i+j)\right|\le\tfrac L4[E_m(u)+E_m(v)],\qquad
\sum_{i,j}|u_i v_j K_w(m+i+j)|\le\frac{L(\|u\|_2^2+\|v\|_2^2)}{8m(m+1)}.
$$

For $\ell(x)=(1-x)/(-\log x)$ the arithmetic and harmonic means bound $\ell$ from above and below. Hence $0\le B(x)=(1+x)\ell(x)/2-x\le(1-x)^2/4$. The moments of $\ell$ give $-\Delta^2(A(k+1)+\tfrac12\log(k+1))=\int_0^1x^k B(x)dx$. Summing two consecutive strings of $r$ differences inserts $(1+x+\cdots+x^{r-1})^2$. The logarithmic term is independent of $r$ after taking the second difference in $m$. In the remaining integral $y=x^r$ bounds the nonnegative density by $y^{m-1}(1-y)^2/(4r)$. Any two such positive forms lie between zero and the same beta form divided by four. Polarization controls their mixed difference. The beta form equals twice $E_m$, including its signs on distinct endpoint shifts.

The singleton bound is $|K_w(m)|\le L/[2m(m+1)(m+2)]$. The positive majorant telescopes along rows. Charging $2|u_i v_j|\le u_i^2+v_j^2$ to those rows gives the absolute estimate. Truncation and rounding toward zero recover the signed form with the same integral approximants on both sides.

Allowing an arbitrary common multiplicity $b$ on multiples of $q$ adds $bA(m)$ to the defect. For an uncentered sum of divisibility classes, $b$ is the sum of their coefficients. The full-prefix bound therefore controls this component separately, including on infinite endpoint supports.
